-- Prove2me | Theorems.Thm_Formalism_REAL_pointwiseAction_mem_admissibleArrays
-- name    : Formalism.REAL.pointwiseAction_mem_admissibleArrays
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:44.566057+00:00
-- url     : https://prove2.me/theorems/9755c8c6-cde0-4c45-a60a-a8ed704cb51b
-- title:
--   REAL: pointwise Action mem admissible Arrays
-- statement:
--   The REAL construction uses the pointwise Action mem admissible Arrays property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L419-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L419-L428

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

theorem Formalism.REAL.pointwiseAction_mem_admissibleArrays {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) {a b : Fin n} (hab : ε a = ε b) :
    ptE E a b F ∈ arrV0 ε E u j := by sorry
