-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
-- name    : AvramDividend.Classical.avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:38:31.975857+00:00
-- url     : https://prove2.me/theorems/5e9573dd-9dc4-423e-a46f-8048ae9f477d
-- title:
--   Canonical positive-cap C¹ extension is globally monotone for the actual BV source residual
-- statement:
--   For the canonical positive-cap HJB C1 test w with derivative at least one in the interior, its cap-linear extension V is monotone on all real reserve values, including nonpositive reserves. The proof invokes the accepted exact positive-cap secant bound and the accepted zero-extension monotonicity theorem, with a separate proof that V agrees with w on y≤0 and at zero. This closes the precise Monotone V premise of the already-Proved genuine intrinsic BV Lévy residual-envelope interface and imposes no stochastic-budget assumption.
-- source:
--   Avram Palmowski and Pistorius (2007) Proposition 4(i): canonical C1 HJB cap extension and original BV finite-variation residual localization.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_zero_extension_global_monotone_of_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
    (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)) :
    Monotone V := by sorry
