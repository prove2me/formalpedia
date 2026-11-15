-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a116_original_intrinsic_gaussian_physical_jump_joint_charfun_20261114
-- name    : AvramDividend.Classical.avram_a116_original_intrinsic_gaussian_physical_jump_joint_charfun_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T23:51:02.674744+00:00
-- url     : https://prove2.me/theorems/96a171dc-0458-4f2e-99d8-1bd4657a8261
-- title:
--   Original finite-activity intrinsic Gaussian residual and physical negative-jump total have factored joint characteristic function
-- statement:
--   For the same original finite-activity spectrally negative Lévy process and its intrinsic Gaussian residual limit, the joint characteristic function of the residual representative and actual full marked negative-jump sum factors into the corresponding marginal characteristic functions. Measurable representatives and source physical jump equality are explicit. No independent Gaussian or Poisson companion, no alternate probability space, and no independence hypothesis are introduced. This is the remaining source Fourier identity needed for original-space Gaussian/jump independence.
-- source:
--   Finite-activity Lévy–Itô decomposition and the original process Lévy-Khintchine exponent. Equivalence with target a95 is Mathlib ProbabilityTheory.indepFun_iff_charFun_prod in pinned Mathlib 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a116_original_intrinsic_gaussian_physical_jump_joint_charfun_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (t : ℝ≥0) (ht : 0 < t)
    (H J : Ω → ℝ)
    (hHMeas : Measurable H) (hJMeas : Measurable J)
    (hHEq : H =ᵐ[P] R t)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    ∀ w : WithLp 2 (ℝ × ℝ),
      charFun (P.map (fun ω => WithLp.toLp 2 (H ω, J ω))) w =
        charFun (P.map H) w.ofLp.1 *
          charFun (P.map J) w.ofLp.2 := by sorry
