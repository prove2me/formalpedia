-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst
-- name    : Formalism.L2.FormalSeriesBounds.ordGE_subst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:14.131658+00:00
-- url     : https://prove2.me/theorems/da332e80-1822-45d5-9bf3-80ba4de9238b
-- title:
--   Formal Series Bounds: ord GE subst
-- statement:
--   The Formal Series Bounds construction uses the ord GE subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L59-L66

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

theorem Formalism.L2.FormalSeriesBounds.ordGE_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE n F) : OrdGE n (subst a F) := by sorry
