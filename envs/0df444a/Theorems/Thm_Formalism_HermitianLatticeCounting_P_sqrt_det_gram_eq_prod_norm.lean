-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sqrt_det_gram_eq_prod_norm
-- name    : Formalism.HermitianLatticeCounting.P.sqrt_det_gram_eq_prod_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:55.270793+00:00
-- url     : https://prove2.me/theorems/89f3ca27-c4f2-4f8e-9c9b-cbf0ac02c110
-- title:
--   P: sqrt det gram eq prod norm
-- statement:
--   The P construction uses the sqrt det gram eq prod norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L294-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L294-L298

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem Formalism.HermitianLatticeCounting.P.sqrt_det_gram_eq_prod_norm {r : ℕ} (a : Fin r → U) :
    Real.sqrt ‖(Matrix.gram ℂ a).det‖ = ∏ i, ‖gramSchmidt ℂ a i‖ := by sorry
