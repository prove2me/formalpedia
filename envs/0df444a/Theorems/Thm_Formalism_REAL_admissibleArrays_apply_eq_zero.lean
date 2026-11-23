-- Prove2me | Theorems.Thm_Formalism_REAL_admissibleArrays_apply_eq_zero
-- name    : Formalism.REAL.admissibleArrays_apply_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:15.863412+00:00
-- url     : https://prove2.me/theorems/1a14e890-7be1-416c-8a59-6967751a1c8a
-- title:
--   REAL: admissible Arrays apply eq zero
-- statement:
--   The REAL construction uses the admissible Arrays apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L207-L212

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

theorem Formalism.REAL.admissibleArrays_apply_eq_zero {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n j}
    (hF : F ∈ arrV0 ε E u j) (α : Fin j → Fin n × Fin n) (hα : ¬ ∀ i, ε (α i).1 ≠ ε (α i).2) :
    F α = 0 := by sorry
