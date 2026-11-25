-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_smul
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:01.946229+00:00
-- url     : https://prove2.me/theorems/e6e8b8d9-24a4-45a0-a439-fd5f1b569e7a
-- title:
--   Formal Series Bounds: subst lin S smul
-- statement:
--   The Formal Series Bounds construction uses the subst lin S smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L208-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L208-L209

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

theorem Formalism.L2.FormalSeriesBounds.subst_linS_smul [Finite σ] (M : τ → σ → C) (r : C) (F : MvPowerSeries σ C) :
    subst (linS M) (r • F) = r • subst (linS M) F := by sorry
