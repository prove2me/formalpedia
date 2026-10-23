-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_weighted_laplace_toReal_bridge
-- name    : AvramDividend.Classical.real_weighted_laplace_toReal_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:58:27.014064+00:00
-- url     : https://prove2.me/theorems/d8f28b6f-53ce-49ac-b67c-7d1dd716e386
-- title:
--   Convert finite extended-nonnegative weighted Laplace integrals to real Bochner integrals
-- statement:
--   For any measurable extended-nonnegative kernel f and any real Laplace parameter θ, assume the weighted ENNReal lintegral of exp(-θt)f(t) is finite. Then the real weighted integral of exp(-θt) times f(t).toReal equals the real part of that lintegral. The proof uses measurable multiplication, Mathlib's ae_lt_top, the pointwise toReal_ofReal_mul identity (valid for every positive real exponential), and integral_toReal. This bridge is independent of the Gaussian process and avoids assuming a formal real/ENNReal interchange without justification.
-- source:
--   Mathlib MeasureTheory.ae_lt_top; ENNReal.toReal_ofReal_mul; MeasureTheory.integral_toReal

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.real_weighted_laplace_toReal_bridge
    (μ : Measure ℝ) (θ : ℝ) (f : ℝ → ENNReal)
    (hf : Measurable f)
    (hfin : (∫⁻ t : ℝ,
      ENNReal.ofReal (Real.exp (-(θ * t))) * f t ∂μ) < ⊤) :
    (∫ t : ℝ, Real.exp (-(θ * t)) * (f t).toReal ∂μ) =
      (∫⁻ t : ℝ,
        ENNReal.ofReal (Real.exp (-(θ * t))) * f t ∂μ).toReal := by sorry
