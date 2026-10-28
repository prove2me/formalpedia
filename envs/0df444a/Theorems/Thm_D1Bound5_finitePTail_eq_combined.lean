-- Prove2me | Theorems.Thm_D1Bound5_finitePTail_eq_combined
-- name    : D1Bound5.finitePTail_eq_combined
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:34.384986+00:00
-- url     : https://prove2.me/theorems/ef08d518-2275-4d3f-afb4-4fd57b452f4c
-- title:
--   Finite PTail eq combined
-- statement:
--   Combine the actual Taylor tails before applying the triangle inequality. In particular the shared s-column terms in H and V cancel here.
-- source:
--   D1Bound5/FinitePAdaptiveTailData.lean, lines 41-52, SHA-256 7413f6f034f62f29a71bf7601fa054eb71ec31e2a6c85f06e6f3607c6aab796c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions

section
namespace D1Bound5









set_option maxHeartbeats 4000000 in

theorem _root_.D1Bound5.finitePTail_eq_combined (a b s c : ℂ) (i : Fin 4) :
    finitePTail a b s c i =
      ∑ j : Fin 3, ∑ l : Fin 3, ![a,b,s] j*finitePRootCoeff a b s i l j*c^(l : ℕ)*
        finiteQHalfRemainder (6+(l : ℕ)) (1/(![a,b,s] j*c)) := by sorry

end D1Bound5
end
