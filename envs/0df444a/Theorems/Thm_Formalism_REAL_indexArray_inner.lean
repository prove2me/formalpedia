-- Prove2me | Theorems.Thm_Formalism_REAL_indexArray_inner
-- name    : Formalism.REAL.indexArray_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:50.572881+00:00
-- url     : https://prove2.me/theorems/432c25ec-859d-4691-a051-9e4a9bdc22c6
-- title:
--   REAL: index Array inner
-- statement:
--   The REAL construction uses the index Array inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L61-L62

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}

theorem Formalism.REAL.indexArray_inner (F G : Arr V n j) : ⟪F, G⟫_ℂ = ∑ α, ⟪F α, G α⟫_ℂ := by sorry
