-- Prove2me | Theorems.Thm_Formalism_NG_GlobalDeterminantRelations_det_relMap_eq
-- name    : Formalism.NG.GlobalDeterminantRelations.det_relMap_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:15.790777+00:00
-- url     : https://prove2.me/theorems/ebbe7a52-7782-44d9-81f3-8b6247710efd
-- title:
--   Global Determinant Relations: det rel Map eq
-- statement:
--   The Global Determinant Relations construction uses the det rel Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean#L44-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean#L44-L68

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.GlobalDeterminantRelations
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')

theorem Formalism.NG.GlobalDeterminantRelations.det_relMap_eq (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R') :
    LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') Θ) =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det := by sorry
