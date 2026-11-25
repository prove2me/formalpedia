-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_pderiv
-- name    : Formalism.L2.FormalSeriesBounds.ordGE_pderiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:13.82114+00:00
-- url     : https://prove2.me/theorems/5869d556-c9f6-4546-bb9e-1f8ba94e1a42
-- title:
--   Formal Series Bounds: ord GE pderiv
-- statement:
--   The Formal Series Bounds construction uses the ord GE pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L98-L101

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

theorem Formalism.L2.FormalSeriesBounds.ordGE_pderiv {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE (n + 1) F) (w : σ) :
    OrdGE n (pderiv C w F) := by sorry
