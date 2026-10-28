-- Prove2me | Theorems.Thm_D1Bound5_bennett_coeff_mul_norm_le
-- name    : D1Bound5.bennett_coeff_mul_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:17.135988+00:00
-- url     : https://prove2.me/theorems/afb44c33-bf3e-4da3-94a2-8bc9472289d2
-- title:
--   Bennett coeff mul norm le
-- statement:
--   Norm coefficient majorants multiply by the actual Cauchy product.
-- source:
--   D1Bound5/BennettCoefficientMajorant.lean, lines 44-59, SHA-256 52f2dc90c9817830bd21c1880dfcf0e6477a59dce71efbcde2deafd50273de8e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5






theorem _root_.D1Bound5.bennett_coeff_mul_norm_le
    (B C : PowerSeries ℂ) (D E : PowerSeries ℝ)
    (hB : ∀ h, ‖PowerSeries.coeff h B‖ ≤ PowerSeries.coeff h D)
    (hC : ∀ h, ‖PowerSeries.coeff h C‖ ≤ PowerSeries.coeff h E) (t : ℕ) :
    ‖PowerSeries.coeff t (B * C)‖ ≤ PowerSeries.coeff t (D * E) := by sorry











end D1Bound5
end
