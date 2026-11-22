-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_apply
-- name    : Formalism.DoubleCosetMeasures.P.lastCoord_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:21.070611+00:00
-- url     : https://prove2.me/theorems/feb7a952-c1d6-4efc-a845-103c12b6f8fe
-- title:
--   P: last Coord apply
-- statement:
--   The P construction uses the last Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L78-L83

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.lastCoord_apply (w : Fin n → K) :
    lastCoord R w = ∑ j : Fin n, if j.val + 1 = n then w j else 0 := by sorry
