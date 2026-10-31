-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_B_1
-- name    : AdaDiscRL.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:32.025383+00:00
-- url     : https://prove2.me/theorems/a3d37ed3-69f9-44c7-be34-8ea1f9b2b325
-- title:
--   Lemma B.1 — partition invariants (corrected: radius-to-confidence clauses)
-- statement:
--   For AdaQL and for AdaMB, on any data sequence, at the end of every episode $k\le K$ and every step $h$:
--
--   1. **(Radius to confidence)** every split (parent) ball $B$ of the tree has $\mathrm{Conf}^k_h(B)\le\mathrm{diam}(B)$; every active ball $B$ with $n^k_h(B)\ge1$ has $\mathrm{diam}(B)<\mathrm{Conf}^k_h(B)$ (for AdaMB: if $B$ has been selected at least once, or if $\widetilde C=4L_Vc\sqrt{\iota}\ge1$); every non-root ball $B$ of the tree has $\mathrm{Conf}^k_h(B)\le2\,\mathrm{diam}(B)$;
--   2. **(Covering)** the active balls of $\mathcal P^k_h$ cover $\mathcal S\times\mathcal A$;
--   3. **(Separation)** two distinct balls of the tree with the same diameter $r$ have centers at distance at least $r$.
--
--   Here $\mathrm{Conf}=4\sqrt{H^3\iota/n}$ for AdaQL and the AdaMB confidence of §3.4, with $\iota=\log(2HK^2/\delta)$.
--
--   Differences from the source:
--   - correction: for any ball B ∈ P_h^k, Conf(B) ≤ diam(B) iff B is a parent ball → parent ⇒ Conf ≤ diam; active with n ≥ 1 ⇒ diam < Conf (AdaQL); active with n ≥ 1 and (selected at least once, or C̃ = 4L_V c√ι ≥ 1) ⇒ diam < Conf (AdaMB); reason: the converse fails for AdaMB at an unselected child when C̃ ≤ 1/4 (the root splits at n = 1; a child has n = 1 and Conf = C̃ ≤ diam while active) (correction C5); n ≥ 1 excludes only the root before its first selection, where the paper's Conf = C̃/0 = ∞ and Lean's x/0 = 0
--   - correction: for any ball B, Conf(B) ≤ 2 diam(B) → for every non-root ball of the tree; reason: the root fails: at n = 1, Conf = C̃ = 4√(H³ι) > 2 = 2 diam(root) for AdaQL (correction C5)
--   - generalization: separation for balls of P_h^k → for all balls of the tree (active or split); reason: active balls are tree balls
--   - generalization: invariants of the algorithm's run → stated for every data sequence (pathwise); reason: the claim is deterministic; a run's data sequence is one data sequence
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma B.1, p.37

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma B.1 (partition invariants)** (arXiv:2110.15843v3, p.37), corrected. For every
`(h, k) ∈ [H] × [K]`, for AdaQL (`Conf = 4√(H³ log(2HK²/δ)/n)`) and for AdaMB
(`Conf` of §3.4, with `L_V, c > 0`):
1. (Radius to confidence) every parent (split) ball `B` has `Conf_h^k(B) ≤ diam(B)`; every active
   ball `B` with `n_h^k(B) ≥ 1` has `diam(B) < Conf_h^k(B)` (for AdaMB: if `B` has been selected, or
   if `C̃ = 4 L_V c √(log(2HK²/δ)) ≥ 1`); every non-root ball `B` of the tree has
   `Conf_h^k(B) ≤ 2 diam(B)`.
2. (Covering) the active balls of `P_h^k` cover `S × A`.
3. (Separation) two balls of the tree with the same diameter `r` have centers at distance `≥ r`.

**Formalization Note.** Pathwise (every data sequence). The printed "for any ball" is false for
an active root (`n = 1`, `Conf = C̃ > 2` for AdaQL), and the printed "only if" is false for AdaMB at
an unselected child when `C̃ ≤ 1/4` (the root splits at `n = 1`; a child has `n = 1` and
`Conf = C̃ ≤ diam`). `n ≥ 1` excludes only the root before its first selection, whose `Conf` is the
paper's `C̃/0 = ∞` (Lean's `x/0 = 0`). The corrected clauses are listed above. -/
theorem lemma_B_1 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    (D : S × A → S × A → ℝ) {H : ℕ} (prm : AdaParams H)
    (P : HierPartition S A ι D prm.dS prm.K) (choose : Finset ι → (ι → ℝ) → ι)
    (hD : IsAdmissibleMetric D) (hH : 1 ≤ H) (hK : 1 ≤ prm.K) (hδ0 : 0 < prm.δ) (hδ1 : prm.δ < 1)
    (hLr : 0 ≤ prm.Lr) (hLV : 0 ≤ prm.LV) (hLT : 0 ≤ prm.LT)
    (hv0 : ∀ h : Fin H, (H : ℝ) - h ≤ prm.v0 h ∧ prm.v0 h ≤ H)
    (hchoose : IsArgmaxRule choose)
    (data : ℕ → EpData S A H) (k : ℕ) (hkK : k ≤ prm.K) (h : Fin H) :
    ((∀ B ∈ (statesQL P prm choose data k h).tree, ¬ isActive P (statesQL P prm choose data k h) B → prm.confQL ((statesQL P prm choose data k h).n B) ≤ P.diam B) ∧
      (∀ B, isActive P (statesQL P prm choose data k h) B → 1 ≤ (statesQL P prm choose data k h).n B →
        P.diam B < prm.confQL ((statesQL P prm choose data k h).n B)) ∧
      (∀ B ∈ (statesQL P prm choose data k h).tree, B ≠ P.root → prm.confQL ((statesQL P prm choose data k h).n B) ≤ 2 * P.diam B) ∧
      (∀ p : S × A, ∃ B, isActive P (statesQL P prm choose data k h) B ∧ p ∈ P.region B) ∧
      (∀ B ∈ (statesQL P prm choose data k h).tree, ∀ B' ∈ (statesQL P prm choose data k h).tree, B ≠ B' → P.diam B = P.diam B' →
        P.diam B ≤ D (P.center B) (P.center B'))) ∧
    ((∀ B ∈ (statesMB P prm choose data k h).tree, ¬ isActive P (statesMB P prm choose data k h) B → prm.confMB ((statesMB P prm choose data k h).n B) ≤ P.diam B) ∧
      (∀ B, isActive P (statesMB P prm choose data k h) B → 1 ≤ (statesMB P prm choose data k h).n B →
        ((∃ j ∈ Finset.Icc 1 k, selAt P choose (statesMB P prm choose) data j h = B) ∨
          1 ≤ 4 * prm.LV * prm.c * Real.sqrt prm.iota) →
        P.diam B < prm.confMB ((statesMB P prm choose data k h).n B)) ∧
      (∀ B ∈ (statesMB P prm choose data k h).tree, B ≠ P.root → prm.confMB ((statesMB P prm choose data k h).n B) ≤ 2 * P.diam B) ∧
      (∀ p : S × A, ∃ B, isActive P (statesMB P prm choose data k h) B ∧ p ∈ P.region B) ∧
      (∀ B ∈ (statesMB P prm choose data k h).tree, ∀ B' ∈ (statesMB P prm choose data k h).tree, B ≠ B' → P.diam B = P.diam B' →
        P.diam B ≤ D (P.center B) (P.center B'))) := by sorry

end AdaDiscRL
