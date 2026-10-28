-- Prove2me | Theorems.Thm_D1Bound5_bennettNumeratorMajorant_hasSum
-- name    : D1Bound5.bennettNumeratorMajorant_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:18.526717+00:00
-- url     : https://prove2.me/theorems/e30f8ae0-f134-4413-b717-e17551fa491c
-- title:
--   Bennett Numerator Majorant has Sum
-- statement:
--   The finite numerator majorant has its ordinary polynomial value as sum.
-- source:
--   D1Bound5/BennettCoefficientMajorant.lean, lines 82-97, SHA-256 52f2dc90c9817830bd21c1880dfcf0e6477a59dce71efbcde2deafd50273de8e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettCoefficientMajorant_Definitions

section
open Finset

namespace D1Bound5














theorem _root_.D1Bound5.bennettNumeratorMajorant_hasSum (U r : ℝ) (k : ℕ) :
    HasSum (fun h : ℕ => PowerSeries.coeff h (bennettNumeratorMajorant U k) * r ^ h)
      ((U + r) ^ (k + 1) / U) := by sorry



end D1Bound5
end
