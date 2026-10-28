-- Prove2me | Theorems.Thm_D1Bound5_bennettPoleMajorant_coeff
-- name    : D1Bound5.bennettPoleMajorant_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:23.949512+00:00
-- url     : https://prove2.me/theorems/13251290-f726-489c-bc0b-4bf1fb14af06
-- title:
--   Bennett Pole Majorant coeff
-- statement:
--   Auxiliary result `bennettPoleMajorant_coeff` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettPositiveSeries.lean, lines 16-19, SHA-256 97c8e1703cfe77445d9777396cd5b2920aa185f7c75649ef58d66b03bb6b026f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettPositiveSeries_Definitions

section
open Finset

namespace D1Bound5



@[simp] theorem _root_.D1Bound5.bennettPoleMajorant_coeff (d : ℝ) (p n : ℕ) :
    PowerSeries.coeff n (bennettPoleMajorant d p) =
      |Ring.choose (-(p : ℝ)) n| * (d⁻¹) ^ (p + n) := by sorry

















end D1Bound5
end
