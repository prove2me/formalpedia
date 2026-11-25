-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_int
-- name    : Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:04:13.024377+00:00
-- url     : https://prove2.me/theorems/34627058-1d53-4938-95d5-b41008fe3b55
-- title:
--   General Germ Zero: gsum K int
-- statement:
--   The General Germ Zero construction uses the gsum K int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L86-L95

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
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

theorem Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_int {V : VF C} (hFI : ∀ k, IntS V (F k)) {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsumK F Γ l j)
  := by sorry
