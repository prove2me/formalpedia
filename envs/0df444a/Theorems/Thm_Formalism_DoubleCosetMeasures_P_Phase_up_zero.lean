-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
-- name    : Formalism.DoubleCosetMeasures.P.Phase.up_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:34.820827+00:00
-- url     : https://prove2.me/theorems/ee7d160a-c25b-48fd-8488-14701489006a
-- title:
--   Phase: up zero
-- statement:
--   The Phase construction uses the up zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L177-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L177-L181

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

theorem Formalism.DoubleCosetMeasures.P.Phase.up_zero {n : ℕ} {y : Matrix (Fin n) (Fin n) K} (hy : IsUpUni y) {i j : Fin n}
    (h : j < i) : y i j = 0 := by sorry
