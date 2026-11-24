-- Prove2me | Theorems.Thm_Formalism_REAL_factorAction_mem_admissibleArrays
-- name    : Formalism.REAL.factorAction_mem_admissibleArrays
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:09.821741+00:00
-- url     : https://prove2.me/theorems/aecfb90f-2837-47d2-b61b-b98aeb01ed52
-- title:
--   REAL: factor Action mem admissible Arrays
-- statement:
--   The REAL construction uses the factor Action mem admissible Arrays property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L377-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L377-L417

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.factorAction_mem_admissibleArrays {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (i : Fin j) {a b : Fin n} (hab : ε a = ε b) :
    factorAction i a b F ∈ arrV0 ε E u j := by sorry
