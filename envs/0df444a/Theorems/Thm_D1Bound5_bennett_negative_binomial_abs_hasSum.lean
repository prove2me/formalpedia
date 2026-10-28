-- Prove2me | Theorems.Thm_D1Bound5_bennett_negative_binomial_abs_hasSum
-- name    : D1Bound5.bennett_negative_binomial_abs_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:10.367762+00:00
-- url     : https://prove2.me/theorems/4e2674c3-14fb-42af-a14b-088346ea0108
-- title:
--   Bennett negative binomial abs has Sum
-- statement:
--   Exact real sum of the absolute negative-binomial series, using the analytic binomial theorem already proved in mathlib.
-- source:
--   D1Bound5/BennettResidualMajorant.lean, lines 52-64, SHA-256 b75484763e5bdb67dae9e19c0cad718baf723c8291fc2f17c55a13171ba3db40. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
An elementary analytic majorant for the actual binomial/homogeneous tail that
arises in Bennett's simultaneous approximants.  In contrast to a coefficient
envelope interface, every coefficient of the series below is specified.

The algebraic identification of the residue moments with homogeneous
polynomials is a separate theorem.  This file does not assume that an arbitrary
series is a Bennett residual.  Once that identification is available, the
specialization n = 3k, s = k + 1/2 gives exactly the eta exponent in the paper.
-/

namespace D1Bound5








theorem _root_.D1Bound5.bennett_negative_binomial_abs_hasSum (q r : ℝ)
    (hq : 0 < q) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun t : ℕ => |Ring.choose (-q) t| * r ^ t)
      (1 / (1 - r) ^ q) := by sorry





end D1Bound5
end
