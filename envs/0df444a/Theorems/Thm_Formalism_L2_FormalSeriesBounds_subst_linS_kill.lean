-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_kill
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_kill
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:28.475877+00:00
-- url     : https://prove2.me/theorems/13049a94-f2ec-544b-a16d-99a10c14ec54
-- title:
--   Formal Series Bounds: subst lin S kill
-- statement:
--   The Formal Series Bounds construction uses the subst lin S kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L258-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L258-L262

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

theorem Formalism.L2.FormalSeriesBounds.subst_linS_kill [Finite σ] (M : τ → σ → C) (P : σ → Prop) (hP : ∀ w, ¬ P w → ∀ c, M c w = 0)
    (F : MvPowerSeries σ C) : subst (linS M) (killV P F) = subst (linS M) F := by sorry
