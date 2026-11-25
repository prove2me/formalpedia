-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_sub
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:09.858131+00:00
-- url     : https://prove2.me/theorems/9620df22-8025-4333-9a50-0fa41b93fa12
-- title:
--   Formal Series Bounds: subst lin S sub
-- statement:
--   The Formal Series Bounds construction uses the subst lin S sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L199-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L199-L200

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

theorem Formalism.L2.FormalSeriesBounds.subst_linS_sub [Finite σ] (M : τ → σ → C) (F G : MvPowerSeries σ C) :
    subst (linS M) (F - G) = subst (linS M) F - subst (linS M) G := by sorry
