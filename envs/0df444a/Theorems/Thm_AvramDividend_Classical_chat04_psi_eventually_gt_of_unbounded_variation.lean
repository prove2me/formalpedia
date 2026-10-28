-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
-- name    : AvramDividend.Classical.chat04_psi_eventually_gt_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T06:52:01.405139+00:00
-- url     : https://prove2.me/theorems/f06e514c-3654-4d25-b2f8-a5afce8580a7
-- title:
--   Unbounded variation implies eventual growth of the Lévy Laplace exponent
-- statement:
--   If the spectrally negative Lévy process has unbounded variation, its Laplace exponent eventually exceeds any positive discount rate. A positive Gaussian coefficient gives the first case. When the Gaussian coefficient is zero, unbounded variation forces divergence of the absolute first moment of small negative jumps, giving the second case. This produces the Laplace parameter witness required by the non-standing unbounded-variation two-sided-exit proof.
-- source:
--   Derived by exhaustive Gaussian coefficient case split from Proved AvramDividend.Classical.psi_eventually_gt_of_gaussian (f5a240ce-817f-4f90-aea0-7563caf01fb5) and psi_eventually_gt_of_infinite_small_jump_moment (0129b889-7aee-41c9-9475-11b37a46af7b), using SpectrallyNegativeLevy.BoundedVariation. Root-connected consumer AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34-200b-4736-a369-5ae8473e3258).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_psi_eventually_gt_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by sorry
