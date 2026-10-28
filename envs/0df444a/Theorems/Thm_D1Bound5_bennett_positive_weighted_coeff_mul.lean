-- Prove2me | Theorems.Thm_D1Bound5_bennett_positive_weighted_coeff_mul
-- name    : D1Bound5.bennett_positive_weighted_coeff_mul
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:31.123225+00:00
-- url     : https://prove2.me/theorems/1a0206c8-3bb7-48fc-9482-16c6d3f5ef1e
-- title:
--   Bennett positive weighted coeff mul
-- statement:
--   Finite weighted coefficient identity, separated from the analytic summation proof so that each proof has its own bounded elaboration budget.
-- source:
--   D1Bound5/BennettPositiveSeries.lean, lines 90-103, SHA-256 97c8e1703cfe77445d9777396cd5b2920aa185f7c75649ef58d66b03bb6b026f. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Finset

namespace D1Bound5














theorem _root_.D1Bound5.bennett_positive_weighted_coeff_mul
    (P Q : PowerSeries ℝ) (r : ℝ) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      (PowerSeries.coeff ij.1 P * r ^ ij.1) *
        (PowerSeries.coeff ij.2 Q * r ^ ij.2)) =
      PowerSeries.coeff n (P * Q) * r ^ n := by sorry







end D1Bound5
end
