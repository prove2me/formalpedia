-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_linS
-- name    : Formalism.L2.FormalSeriesBounds.hasSubst_linS
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:54.646889+00:00
-- url     : https://prove2.me/theorems/2a123a1f-ee64-497a-926e-3f2c4129c90e
-- title:
--   Formal Series Bounds: has Subst lin S
-- statement:
--   The Formal Series Bounds construction uses the has Subst lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L193-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L193-L194

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
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.hasSubst_linS [Finite σ] (M : τ → σ → C) : HasSubst (linS M) := by sorry
