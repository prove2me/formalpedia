-- Prove2me | Theorems.Thm_D1Bound5_bennett_choose_tail_identity
-- name    : D1Bound5.bennett_choose_tail_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:28.855705+00:00
-- url     : https://prove2.me/theorems/4ca17b95-2d96-42bc-990c-2b5f166854d5
-- title:
--   Bennett choose tail identity
-- statement:
--   Exact coefficient identity responsible for cancellation of the homogeneous coefficient counting factor.
-- source:
--   D1Bound5/BennettResidualMajorant.lean, lines 39-50, SHA-256 b75484763e5bdb67dae9e19c0cad718baf723c8291fc2f17c55a13171ba3db40. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.bennett_choose_tail_identity (s : ℝ) (n t : ℕ) :
    |Ring.choose s (n + t)| * (Nat.choose (n + t) t : ℝ) =
      |Ring.choose s n| * |Ring.choose (s - n) t| := by sorry







end D1Bound5
end
