-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_scale_value_from_renewal_density
-- name    : AvramDividend.Classical.esscher_scale_value_from_renewal_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:54:57.24447+00:00
-- url     : https://prove2.me/theorems/b78e86e1-9cc9-4762-ab08-3f646befbcd6
-- title:
--   Recover positive Esscher scale values from a finite renewal atom and density
-- statement:
--   For a canonical Esscher renewal measure with a zero atom, nonnegative real density and finite mass, translate the pointwise Laplace-identified cumulative identity into the exact exponential-times-primitive formula for W on positive initial capital. This eliminates one representation gap in the bounded-variation zero-right derivative proof.
-- source:
--   Proved geometric_atom_plus_real_density_full_cumulative (9249f2c7), Real.exp_add and the canonical BV geometric renewal scale identity.

import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_full_cumulative
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Convert a finite real-density renewal measure into the positive Esscher scale primitive. -/
theorem esscher_scale_value_from_renewal_density
    (W : ℝ → ℝ) (φ r : ℝ) (f : ℝ → ℝ)
    (hr : 0 ≤ r) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (hβneg : β (Iio (0 : ℝ)) = 0)
    (hβfin : β Set.univ ≠ ⊤)
    (hscale : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal)
    (hfi : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (x : ℝ) (hx : 0 < x) :
    W x = Real.exp (φ * x) *
      (r + r * ∫ y in (0 : ℝ)..x, f y) := by sorry

end AvramDividend.Classical
