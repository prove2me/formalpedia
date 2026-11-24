-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_gram_eq_prod_gramSchmidt_norm_sq
-- name    : Formalism.HermitianLatticeCounting.P.det_gram_eq_prod_gramSchmidt_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:28.488812+00:00
-- url     : https://prove2.me/theorems/ba769c15-1822-45ca-83ce-37df9082c372
-- title:
--   P: det gram eq prod gram Schmidt norm sq
-- statement:
--   The P construction uses the det gram eq prod gram Schmidt norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L279-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L279-L292

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

theorem Formalism.HermitianLatticeCounting.P.det_gram_eq_prod_gramSchmidt_norm_sq {r : ℕ} (a : Fin r → U) :
    (Matrix.gram ℂ a).det = ∏ i, ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2) := by sorry
