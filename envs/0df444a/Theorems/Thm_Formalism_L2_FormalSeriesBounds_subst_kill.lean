-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_kill
-- name    : Formalism.L2.FormalSeriesBounds.subst_kill
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:24.353788+00:00
-- url     : https://prove2.me/theorems/808aa157-3470-5520-bf20-5ba989a27503
-- title:
--   Formal Series Bounds: subst kill
-- statement:
--   The Formal Series Bounds construction uses the subst kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L74-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L74-L88

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

theorem Formalism.L2.FormalSeriesBounds.subst_kill [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (P : σ → Prop)
    (hP : ∀ w, ¬ P w → a w = 0) (F : MvPowerSeries σ C) :
    subst a (killV P F) = subst a F := by sorry
