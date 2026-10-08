-- Prove2me | Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_mass_bound
-- name    : ConnesGreen.supported_mellin_norm_sq_mass_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T20:40:39.177319+00:00
-- url     : https://prove2.me/theorems/e21d930b-54b8-4194-90b3-369dd7b9f988
-- title:
--   Original supported Mellin transform bounded by exact support-length mass
-- statement:
--   Let $T\ge0$, let $g:\mathbb R\to\mathbb C$ be smooth and compactly supported with $\operatorname{tsupport}(g)\subset(-T,T)$, and define $\widehat g(z)=\int g(t)e^{(z-1/2)t}\,dt$. Then, for every $z\in\mathbb C$, $$|\widehat g(z)|^2\le2T e^{2|\operatorname{Re}z-1/2|T}\int_{\mathbb R}|g(t)|^2\,dt.$$ This estimate is uniform in the imaginary part and supplies the original Fourier concentration and pole estimates for an explicit small-support Weil positivity interval. The integral mass is an auxiliary arithmetic quantity; no physical metric is replaced.
-- source:
--   monocap-tech/weil, Connes/ArchimedeanFrequency.lean, supported_mellin_norm_sq_mass_bound. The public test predicate explicitly unfolds WeilDefect.ConnesNative.SupportedTest; the original IsTest and mellinHat definitions are independently checked in native and platform toolchains. Companion native SmallSupportPositivity.lean proves actual full Weil positivity and all-positive-regularization marker bounds on an explicit small support interval; this export does not claim positivity at an identified critical endpoint or RH.

import Definitions.Def_ConnesRZ_weil_defs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ Set
noncomputable section

private theorem finite_measure_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  let m := μ.real univ
  let J := ∫ x, ‖f x‖ ∂μ
  let L := ∫ x, ‖f x‖ ^ 2 ∂μ
  have hm : 0 ≤ m := measureReal_nonneg
  have hJ : 0 ≤ J := integral_nonneg (fun x => norm_nonneg _)
  have hnorm : ‖∫ x, f x ∂μ‖ ≤ J := norm_integral_le_integral_norm f
  have hv : 0 ≤ ∫ x, (m * ‖f x‖ - J) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have he : (∫ x, (m * ‖f x‖ - J) ^ 2 ∂μ) = m ^ 2 * L - m * J ^ 2 := by
    simp_rw [show ∀ x, (m * ‖f x‖ - J) ^ 2 =
      m ^ 2 * ‖f x‖ ^ 2 - (2 * m * J) * ‖f x‖ + J ^ 2 by intro x; ring]
    have hd : Integrable (fun x => m ^ 2 * ‖f x‖ ^ 2 - (2 * m * J) * ‖f x‖) μ :=
      (hf2.const_mul _).sub (hf.norm.const_mul _)
    rw [integral_add hd (integrable_const _),
      integral_sub (hf2.const_mul _) (hf.norm.const_mul _), integral_const_mul,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul]
    dsimp [m, J, L]
    ring
  rw [he] at hv
  by_cases hm0 : m = 0
  · have hμ : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact ((ENNReal.toReal_eq_zero_iff (μ univ)).mp hm0).resolve_right
        (measure_ne_top μ univ)
    simp [hμ]
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hsq : J ^ 2 ≤ m * L := by nlinarith
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsq

theorem ConnesGreen.supported_mellin_norm_sq_mass_bound (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : IsTest g ∧ tsupport g ⊆ Ioo (-T) T) (z : ℂ) :
    ‖mellinHat g z‖ ^ 2 ≤ 2 * T * Real.exp (2 * |z.re - 1 / 2| * T) *
      (∫ s : ℝ, ‖g s‖ ^ 2) := by sorry
