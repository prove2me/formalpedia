-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_dVar_eq_pderiv
-- name    : Formalism.L2.FormalSeriesBounds.dVar_eq_pderiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:16.21857+00:00
-- url     : https://prove2.me/theorems/67628b4c-ce29-46b2-ab2b-4b31d9d5a6e8
-- title:
--   Formal Series Bounds: d Var eq pderiv
-- statement:
--   The Formal Series Bounds construction uses the d Var eq pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L90-L96

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

theorem Formalism.L2.FormalSeriesBounds.dVar_eq_pderiv {C : Type} [Field C] {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = pderiv C w F := by sorry
