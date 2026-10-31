-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_B_2
-- name    : AdaDiscRL.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:29.108725+00:00
-- url     : https://prove2.me/theorems/bed08564-384e-4036-bac5-a7e963ba76cf
-- title:
--   Lemma B.2 — sample counts per ball (corrected: $\lceil n_{\max}\rceil$, root count, $\widetilde C\ge1$ for AdaMB)
-- statement:
--   Write $\mathrm{Conf}=\widetilde C/n^\alpha$, with $\widetilde C=4\sqrt{H^3\iota}$, $\alpha=\tfrac12$ for AdaQL and $\widetilde C=4L_Vc\sqrt\iota$, $\alpha=\tfrac12$ ($d_{\mathcal S}\le2$) or $\alpha=1/d_{\mathcal S}$ ($d_{\mathcal S}>2$) for AdaMB, and set
--   $$
--   n_{\min}(B)=\Big(\frac{\widetilde C}{2\,\mathrm{diam}(B)}\Big)^{1/\alpha},\qquad n_{\max}(B)=\Big(\frac{\widetilde C}{\mathrm{diam}(B)}\Big)^{1/\alpha}.
--   $$
--   On any data sequence, at the end of every episode $k\le K$ and step $h$:
--
--   1. every non-root ball $B$ of the tree has $n_{\min}(B)\le n^k_h(B)$;
--   2. every ball $B$ of the tree below the last level has $n^k_h(B)\le\lceil n_{\max}(B)\rceil$ (for AdaMB, when $\widetilde C\ge1$);
--   3. the root is selected in at most $\lceil\widetilde C^{1/\alpha}\rceil$ of the episodes $1,\dots,k$.
--
--   For AdaMB, $L_V,c>0$ are assumed. These counts bound how often a ball of each radius can be selected, which drives the zooming-dimension sum in Theorem F.3.
--
--   Differences from the source:
--   - correction: n_h^k(B) ≤ n_max(B) → n_h^k(B) ≤ ⌈n_max(B)⌉; reason: a ball splits at the first integer count with Conf ≤ diam, which can exceed the real n_max (correction C6)
--   - correction: the root is selected only once → the root is selected at most ⌈C̃^{1/α}⌉ times; reason: the root splits once C̃/n^α ≤ 1, i.e. after about C̃^{1/α} selections; for AdaQL C̃ > 2 (correction C6)
--   - correction: AdaMB upper bound for any L_V, c → AdaMB upper bound when C̃ = 4 L_V c √ι ≥ 1; AdaMB clauses with L_V, c > 0; reason: with C̃ = 0.01, α = 1/2 a level-1 child inherits n = 1, is selected once and splits at n = 2 > ⌈(2C̃)²⌉ = 1; with L_V = 0 the root is selected once while ⌈0⌉ = 0
--   - generalization: child balls of P_h^K at the last episode → every ball of the tree at the end of any episode k ≤ K; reason: includes the source's balls
--   - generalization: invariants of the algorithm's run → stated for every data sequence (pathwise); reason: the claim is deterministic; a run's data sequence is one data sequence
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma B.2, p.37

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma B.2 (sample counts)** (arXiv:2110.15843v3, p.37), corrected. Write
`Conf(B) = C̃/n(B)^α` (AdaQL: `C̃ = 4√(H³ log(2HK²/δ))`, `α = 1/2`; AdaMB: `C̃ = 4 L_V c √(log(2HK²/δ))`,
`α = 1/2` if `d_S ≤ 2` and `α = 1/d_S` if `d_S > 2`), `n_min(B) = (C̃/(2 diam B))^{1/α}` and
`n_max(B) = (C̃/diam B)^{1/α}`. For every non-root ball `B` of the tree at the end of episode `k`,
`n_min(B) ≤ n_h^k(B)`; for every ball below the last level, `n_h^k(B) ≤ ⌈n_max(B)⌉` (for AdaMB when
`C̃ ≥ 1`); and the root is selected in at most `⌈C̃^{1/α}⌉` episodes (AdaMB with `L_V, c > 0`).

**Formalization Note.** Pathwise. Corrections: the printed `n ≤ n_max` fails by rounding (a ball
splits at the first integer count `≥ n_max`); the root is selected about `C̃^{1/α}` times, not once;
for AdaMB the root clause needs `C̃ > 0` (with `L_V = 0` the root is selected once and `⌈0⌉ = 0`),
and the upper bound needs `C̃ ≥ 1` (with `C̃ = 0.01`, `α = 1/2` a level-1 child inherits
`n = 1`, is selected once and splits at `n = 2 > ⌈(2C̃)²⌉ = 1`). A ball of the last level `K` has no
children and is never split. -/
theorem lemma_B_2 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    (D : S × A → S × A → ℝ) {H : ℕ} (prm : AdaParams H)
    (P : HierPartition S A ι D prm.dS prm.K) (choose : Finset ι → (ι → ℝ) → ι)
    (hD : IsAdmissibleMetric D) (hH : 1 ≤ H) (hK : 1 ≤ prm.K) (hδ0 : 0 < prm.δ) (hδ1 : prm.δ < 1)
    (hLr : 0 ≤ prm.Lr) (hLV : 0 ≤ prm.LV) (hLT : 0 ≤ prm.LT)
    (hv0 : ∀ h : Fin H, (H : ℝ) - h ≤ prm.v0 h ∧ prm.v0 h ≤ H)
    (hchoose : IsArgmaxRule choose)
    (data : ℕ → EpData S A H) (k : ℕ) (hkK : k ≤ prm.K) (h : Fin H) :
    ((∀ B ∈ (statesQL P prm choose data k h).tree, B ≠ P.root →
        ((4 * Real.sqrt ((H : ℝ) ^ 3 * prm.iota)) / (2 * P.diam B)) ^ ((2 : ℝ)) ≤ ((statesQL P prm choose data k h).n B : ℝ)) ∧
      (∀ B ∈ (statesQL P prm choose data k h).tree, P.level B < prm.K →
        ((statesQL P prm choose data k h).n B : ℝ) ≤ ((⌈((4 * Real.sqrt ((H : ℝ) ^ 3 * prm.iota)) / P.diam B) ^ ((2 : ℝ))⌉ : ℤ) : ℝ)) ∧
      (((Finset.Icc 1 k).filter (fun j => selAt P choose (statesQL P prm choose) data j h = P.root)).card : ℝ) ≤
        ((⌈((4 * Real.sqrt ((H : ℝ) ^ 3 * prm.iota)) : ℝ) ^ ((2 : ℝ))⌉ : ℤ) : ℝ)) ∧
    (0 < prm.LV → 0 < prm.c →
      ((∀ B ∈ (statesMB P prm choose data k h).tree, B ≠ P.root →
        ((4 * prm.LV * prm.c * Real.sqrt prm.iota) / (2 * P.diam B)) ^ ((if prm.dS ≤ 2 then (2 : ℝ) else (prm.dS : ℝ))) ≤ ((statesMB P prm choose data k h).n B : ℝ)) ∧
      (1 ≤ 4 * prm.LV * prm.c * Real.sqrt prm.iota → ∀ B ∈ (statesMB P prm choose data k h).tree, P.level B < prm.K →
        ((statesMB P prm choose data k h).n B : ℝ) ≤ ((⌈((4 * prm.LV * prm.c * Real.sqrt prm.iota) / P.diam B) ^ ((if prm.dS ≤ 2 then (2 : ℝ) else (prm.dS : ℝ)))⌉ : ℤ) : ℝ)) ∧
      (((Finset.Icc 1 k).filter (fun j => selAt P choose (statesMB P prm choose) data j h = P.root)).card : ℝ) ≤
        ((⌈((4 * prm.LV * prm.c * Real.sqrt prm.iota) : ℝ) ^ ((if prm.dS ≤ 2 then (2 : ℝ) else (prm.dS : ℝ)))⌉ : ℤ) : ℝ))) := by sorry

end AdaDiscRL
