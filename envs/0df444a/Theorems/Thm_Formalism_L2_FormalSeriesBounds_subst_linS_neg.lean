-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_neg
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:52.642133+00:00
-- url     : https://prove2.me/theorems/afd6bd18-5f67-463f-a2a6-a1e6bb313784
-- title:
--   Formal Series Bounds: subst lin S neg
-- statement:
--   The Formal Series Bounds construction uses the subst lin S neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L220-L223

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

theorem Formalism.L2.FormalSeriesBounds.subst_linS_neg [Finite σ] (M : τ → σ → C) (F : MvPowerSeries σ C) :
    subst (linS M) (-F) = -subst (linS M) F := by sorry
