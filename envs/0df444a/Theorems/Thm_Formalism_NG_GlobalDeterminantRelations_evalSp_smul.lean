-- Prove2me | Theorems.Thm_Formalism_NG_GlobalDeterminantRelations_evalSp_smul
-- name    : Formalism.NG.GlobalDeterminantRelations.evalSp_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:14.522895+00:00
-- url     : https://prove2.me/theorems/aa65c780-8948-4f8c-98af-bb28066299b1
-- title:
--   Global Determinant Relations: eval Sp smul
-- statement:
--   The Global Determinant Relations construction uses the eval Sp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean#L20-L22

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

theorem Formalism.NG.GlobalDeterminantRelations.evalSp_smul (r : R') (v : EvalSp O d R' x') (a : d) :
    (r • v : d → FractionRing O) a =
      ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b := by sorry
