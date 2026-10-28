-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedTaylor_eval_norm_le_coeff
-- name    : D1Bound5.bennettClearedTaylor_eval_norm_le_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:33.132385+00:00
-- url     : https://prove2.me/theorems/bcd7c283-67a3-4308-b210-472cba822bcc
-- title:
--   Bennett Cleared Taylor eval norm le coeff
-- statement:
--   The actual complex local residue Taylor expression is bounded by the coefficient of the explicit positive numerator/pole majorant.
-- source:
--   D1Bound5/BennettCoefficientMajorant.lean, lines 99-138, SHA-256 52f2dc90c9817830bd21c1880dfcf0e6477a59dce71efbcde2deafd50273de8e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettCoefficientMajorant_Definitions

section
open Finset

namespace D1Bound5
















theorem _root_.D1Bound5.bennettClearedTaylor_eval_norm_le_coeff
    (k t : ℕ) (ht : t ≤ k) (a N : ℂ)
    (B : PowerSeries ℂ) (D : PowerSeries ℝ)
    (hU : 0 < ‖N + a‖)
    (hB : ∀ h, ‖PowerSeries.coeff h B‖ ≤ PowerSeries.coeff h D) :
    ‖(bennettClearedTaylor k t (1 / 2 : ℂ) a B).eval N‖ ≤
      PowerSeries.coeff t (bennettNumeratorMajorant ‖N + a‖ k * D) := by sorry

end D1Bound5
end
