-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst_linS
-- name    : Formalism.L2.FormalSeriesBounds.ordGE_subst_linS
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:57.142016+00:00
-- url     : https://prove2.me/theorems/53bb4460-b5d8-4f28-ab9a-fd007661a95c
-- title:
--   Formal Series Bounds: ord GE subst lin S
-- statement:
--   The Formal Series Bounds construction uses the ord GE subst lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L230-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L230-L231

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

theorem Formalism.L2.FormalSeriesBounds.ordGE_subst_linS [Finite σ] (M : τ → σ → C) {F : MvPowerSeries σ C} {n : ℕ}
    (hF : OrdGE n F) : OrdGE n (subst (linS M) F) := by sorry
