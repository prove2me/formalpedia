-- Prove2me | Theorems.Thm_Formalism_REAL_admissibleArrays_apply_mem
-- name    : Formalism.REAL.admissibleArrays_apply_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:38.907079+00:00
-- url     : https://prove2.me/theorems/4e1c5412-0e68-409a-ae5f-cc20cefafa11
-- title:
--   REAL: admissible Arrays apply mem
-- statement:
--   The REAL construction uses the admissible Arrays apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L198-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L198-L205

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

theorem Formalism.REAL.admissibleArrays_apply_mem {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n j}
    (hF : F ∈ arrV0 ε E u j) (α : Fin j → Fin n × Fin n) : F α ∈ kSpan ε E u := by sorry
