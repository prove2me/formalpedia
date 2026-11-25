-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_linS
-- name    : Formalism.L2.FormalSeriesBounds.pderiv_linS
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:26.819174+00:00
-- url     : https://prove2.me/theorems/7b9782a8-2581-4649-b247-041f7cb39b33
-- title:
--   Formal Series Bounds: pderiv lin S
-- statement:
--   The Formal Series Bounds construction uses the pderiv lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L238-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L238-L245

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

theorem Formalism.L2.FormalSeriesBounds.pderiv_linS (M : τ → σ → C) (b : τ) (w : σ) :
    pderiv C b (linS M w) = MvPowerSeries.C (M b w) := by sorry
