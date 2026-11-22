-- Prove2me | Theorems.Thm_Formalism_REAL_firstPositionSlice_apply
-- name    : Formalism.REAL.firstPositionSlice_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:28.394234+00:00
-- url     : https://prove2.me/theorems/927a8cae-8f60-4063-b7df-09e62b93e184
-- title:
--   REAL: first Position Slice apply
-- statement:
--   The REAL construction uses the first Position Slice apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L30-L32

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

theorem Formalism.REAL.firstPositionSlice_apply (α' : Fin j → Fin n × Fin n) (F : Arr V n (j+1)) (β : Fin 1 → Fin n × Fin n) :
    sliceLin V n α' F β = F (Fin.cons (β 0) α') := by sorry
