-- Prove2me | Theorems.Thm_Formalism_NG_gen_relMap_apply
-- name    : Formalism.NG.gen_relMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:59.111526+00:00
-- url     : https://prove2.me/theorems/4c664076-09dd-4105-9930-f889170599f8
-- title:
--   NG: gen rel Map apply
-- statement:
--   The NG construction uses the gen rel Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L13-L14

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.gen_relMap_apply {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b O) (v : b → KO O) (i : a) :
    relMap O (KO O) X v i = ∑ j, X i j • v j := by sorry
