-- Prove2me | Theorems.Thm_Formalism_REAL_re_inner_self_indexArray
-- name    : Formalism.REAL.re_inner_self_indexArray
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:55.859126+00:00
-- url     : https://prove2.me/theorems/b034163c-7c0e-4e68-901c-1164f1a296a4
-- title:
--   REAL: re inner self index Array
-- statement:
--   The REAL construction uses the re inner self index Array property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L504-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L504-L508

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

theorem Formalism.REAL.re_inner_self_indexArray (F : Arr V n j) : (⟪F, F⟫_ℂ).re = ‖F‖ ^ 2 := by sorry
