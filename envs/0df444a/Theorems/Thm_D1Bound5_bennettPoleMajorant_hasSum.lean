-- Prove2me | Theorems.Thm_D1Bound5_bennettPoleMajorant_hasSum
-- name    : D1Bound5.bennettPoleMajorant_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:27.526932+00:00
-- url     : https://prove2.me/theorems/111e4990-b8d6-45f6-868b-21ca7d88b32c
-- title:
--   Bennett Pole Majorant has Sum
-- statement:
--   The actual weighted sum of the positive pole majorant, including pole order zero. The radius is strictly smaller than the positive displacement.
-- source:
--   D1Bound5/BennettPositiveSeries.lean, lines 36-78, SHA-256 97c8e1703cfe77445d9777396cd5b2920aa185f7c75649ef58d66b03bb6b026f. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.bennettPoleMajorant_hasSum
    (d r : ℝ) (p : ℕ) (hd : 0 < d) (hr0 : 0 ≤ r) (hrd : r < d) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (bennettPoleMajorant d p) * r ^ n)
      ((d-r)⁻¹ ^ p) := by sorry











end D1Bound5
end
