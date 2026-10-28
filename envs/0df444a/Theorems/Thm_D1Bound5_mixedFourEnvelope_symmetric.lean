-- Prove2me | Theorems.Thm_D1Bound5_mixedFourEnvelope_symmetric
-- name    : D1Bound5.mixedFourEnvelope_symmetric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:33:40.730722+00:00
-- url     : https://prove2.me/theorems/d9d853eb-214f-4139-8fd7-9b94fe7b1596
-- title:
--   Mixed Four Envelope symmetric
-- statement:
--   Auxiliary result `mixedFourEnvelope_symmetric` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/WeightedRowCertificate.lean, lines 22-33, SHA-256 24e91527c5f644ec2b6289935e81e061377a21fe404f3e2ef431b87e3d5e91b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_WeightedRowCertificate_Definitions

section
namespace D1Bound5









theorem _root_.D1Bound5.mixedFourEnvelope_symmetric (i j : Fin 4) :
    mixedFourEnvelope i j = mixedFourEnvelope j i := by sorry





end D1Bound5

namespace D1Bound5





end D1Bound5
end
