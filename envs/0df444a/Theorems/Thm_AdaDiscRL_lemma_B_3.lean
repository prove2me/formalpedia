-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_B_3
-- name    : AdaDiscRL.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:37.388371+00:00
-- url     : https://prove2.me/theorems/e768d9c3-5dda-4cfe-b0d4-9e6bbedd228b
-- title:
--   Lemma B.3 — ancestral bias is at most $4\,\mathrm{diam}(B)$ (corrected: $\widetilde C\ge1$ for AdaMB)
-- statement:
--   On any data sequence, fix an episode $k\in[K]$, a step $h$ and an active ball $B\in\mathcal P^k_h$, and let $k_1<\dots<k_t\le k$ be the episodes at which $B$ or its ancestors were selected at step $h$. Then for AdaQL
--   $$
--   \sum_{i=1}^t\alpha^i_t\,\mathrm{diam}(B^{k_i}_h)\le4\,\mathrm{diam}(B),
--   $$
--   and for AdaMB, if $\widetilde C=4L_Vc\sqrt{\log(2HK^2/\delta)}\ge1$,
--   $$
--   \frac1t\sum_{i=1}^t\mathrm{diam}(B^{k_i}_h)\le4\,\mathrm{diam}(B).
--   $$
--   The estimates of a ball aggregate data from its ancestors; this lemma bounds the resulting bias by the ball's own diameter.
--
--   Differences from the source:
--   - correction: AdaMB average bound for any L_V, c → AdaMB bound when C̃ = 4 L_V c √ι ≥ 1; reason: if C̃ ≤ 2^{−6} every selection splits, so a ball of level 6 reached along one path has t = 6 encounters at levels 0, …, 5, with average diameter (2 − 2^{−5})/6 ≈ 0.33 > 4 · 2^{−6} ≈ 0.06 (a numerical sweep found ratios up to 241 for small C̃ and none above 0.77 for C̃ ≥ 1)
--   - encoding: h, k ∈ [K] × [K] → h : Fin H, k ∈ [K]; reason: typo for [H] × [K]
--   - generalization: invariants of the algorithm's run → stated for every data sequence (pathwise); reason: the claim is deterministic; a run's data sequence is one data sequence
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma B.3, p.38

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma B.3 (ancestral bias)** (arXiv:2110.15843v3, p.38), corrected for AdaMB. For
`(h, k) ∈ [H] × [K]` and an active ball `B ∈ P_h^k`, let `t = n_h^k(B)` and `k₁ < ⋯ < k_t ≤ k` the
episodes at which `B` or its ancestors were selected at step `h`. For AdaQL,
`Σ_{i=1}^t α_t^i diam(B_h^{k_i}) ≤ 4 diam(B)`; for AdaMB, if `C̃ = 4 L_V c √(log(2HK²/δ)) ≥ 1`,
`(1/t) Σ_{i=1}^t diam(B_h^{k_i}) ≤ 4 diam(B)`.

**Formalization Note.** Pathwise; `[K] × [K]` on the page is read `[H] × [K]`. AdaMB correction
(`C̃ ≥ 1` added): if `C̃ ≤ 2^{−6}` every selection splits, so a ball `B` of level 6 reached along one
path has `t = 6` encounters, one per level `0, …, 5`, with average diameter `(2 − 2^{−5})/6 ≈ 0.33 >
4 · 2^{−6}`. -/
theorem lemma_B_3 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    (D : S × A → S × A → ℝ) {H : ℕ} (prm : AdaParams H)
    (P : HierPartition S A ι D prm.dS prm.K) (choose : Finset ι → (ι → ℝ) → ι)
    (hD : IsAdmissibleMetric D) (hH : 1 ≤ H) (hK : 1 ≤ prm.K) (hδ0 : 0 < prm.δ) (hδ1 : prm.δ < 1)
    (hLr : 0 ≤ prm.Lr) (hLV : 0 ≤ prm.LV) (hLT : 0 ≤ prm.LT)
    (hv0 : ∀ h : Fin H, (H : ℝ) - h ≤ prm.v0 h ∧ prm.v0 h ≤ H)
    (hchoose : IsArgmaxRule choose)
    (data : ℕ → EpData S A H) (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ prm.K) (h : Fin H) :
    (∀ B, isActive P (statesQL P prm choose data k h) B →
      ∑ i : Fin (encounters P choose (statesQL P prm choose) data k h B).card,
        VLearning.CCE.lrW H (encounters P choose (statesQL P prm choose) data k h B).card (i.val + 1) *
          P.diam (selAt P choose (statesQL P prm choose) data
            (encEp P choose (statesQL P prm choose) data k h B i) h) ≤ 4 * P.diam B) ∧
    (1 ≤ 4 * prm.LV * prm.c * Real.sqrt prm.iota →
      ∀ B, isActive P (statesMB P prm choose data k h) B →
        (1 / ((encounters P choose (statesMB P prm choose) data k h B).card : ℝ)) * ∑ i : Fin (encounters P choose (statesMB P prm choose) data k h B).card,
          P.diam (selAt P choose (statesMB P prm choose) data
            (encEp P choose (statesMB P prm choose) data k h B i) h) ≤ 4 * P.diam B) := by sorry

end AdaDiscRL
