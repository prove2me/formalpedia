-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_identity_5_5
-- name    : BanditCovariates.ABSE.identity_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:10:46.126456+00:00
-- url     : https://prove2.me/theorems/d7b01771-d1ae-4744-a6d9-820e7d7058ab
-- title:
--   (5.5), p. 24 — r^born_n(B) = r^live_n(B) + Σ_{B′∈burst(B)} r^born_n(B′)
-- statement:
--   For a valid cell $B$ in the truncated dyadic tree, along a sample path whose first $n$ covariates lie in the unit cube,
--
--   $$r_n^{\mathrm{born}}(B)=r_n^{\mathrm{live}}(B)+\sum_{B'\in\operatorname{burst}(B)}r_n^{\mathrm{born}}(B').$$
--
--   No child of a maximum-depth cell is born, so its child sum is zero. This pathwise identity decomposes regret over the tree.
--
--   **Formalization Note** A half-open boundary assignment makes the pathwise partition exact; boundary choices are null under the paper's density condition.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 24, (5.5)

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_ProofObjects

noncomputable section

namespace BanditCovariates.ABSE

/-- Display (5.5), p. 24: regret on a born node decomposes into its live
regret and its children's born regret, path by path. -/
theorem identity_5_5 {d K n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (hK : 0 < K) (β L : ℝ)
    (B : Cell d) (hB : ValidCell B) (hdepth : B.depth ≤ k0 d K n β)
    (ω : Ω) (hX : ∀ t < n, M.X t ω ∈ cube d) :
    bornRegret (n := n) M hK β L B ω =
      liveRegret (n := n) M hK β L B ω +
        ∑ C ∈ burst B, bornRegret (n := n) M hK β L C ω := by sorry

end BanditCovariates.ABSE
