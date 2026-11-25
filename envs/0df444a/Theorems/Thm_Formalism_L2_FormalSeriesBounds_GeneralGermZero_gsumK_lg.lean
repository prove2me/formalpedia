-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_lg
-- name    : Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_lg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:10.103777+00:00
-- url     : https://prove2.me/theorems/a2afdff3-a9e7-4a62-8f26-01b0961d7585
-- title:
--   General Germ Zero: gsum K lg
-- statement:
--   The General Germ Zero construction uses the gsum K lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L97-L106

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
variable {F : κ → MvPowerSeries (Fin 2 × κ) C} (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
include hF0

theorem Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_lg {lg : κ → MvPowerSeries κ C} (hadd : LgAdd F lg) (hlg0 : ∀ k, MvPowerSeries.constantCoeff (lg k) = 0)
    {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : κ) :
    ∀ l : List ι, MvPowerSeries.subst (gsumK F Γ l) (lg i) = (l.map fun c => MvPowerSeries.subst (Γ c) (lg i)).sum
  := by sorry
