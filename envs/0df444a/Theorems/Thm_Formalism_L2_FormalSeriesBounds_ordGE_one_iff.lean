-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_one_iff
-- name    : Formalism.L2.FormalSeriesBounds.ordGE_one_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:24:23.750317+00:00
-- url     : https://prove2.me/theorems/28c6468e-7ba5-5432-ab15-2cee51547612
-- title:
--   Formal Series Bounds: ord GE one iff
-- statement:
--   The Formal Series Bounds construction uses the ord GE one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L18-L28

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*}

theorem Formalism.L2.FormalSeriesBounds.ordGE_one_iff (f : MvPowerSeries τ C) : OrdGE 1 f ↔ constantCoeff f = 0 := by sorry
