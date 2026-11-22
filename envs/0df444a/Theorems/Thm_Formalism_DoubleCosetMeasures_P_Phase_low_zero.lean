-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
-- name    : Formalism.DoubleCosetMeasures.P.Phase.low_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:15.981802+00:00
-- url     : https://prove2.me/theorems/0562bcb7-77d5-4cd0-8bac-17b3d3a2a8c6
-- title:
--   Phase: low zero
-- statement:
--   The Phase construction uses the low zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L171-L175

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
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
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]

theorem Formalism.DoubleCosetMeasures.P.Phase.low_zero {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) {i j : Fin n}
    (h : i < j) : x i j = 0 := by sorry
