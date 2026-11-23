-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_simple_add_zero
-- name    : Formalism.DoubleCosetMeasures.P.Phase.simple_add_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:09.490962+00:00
-- url     : https://prove2.me/theorems/d8e4d04a-c1d4-45ab-800c-0814d04facf0
-- title:
--   Phase: simple add zero
-- statement:
--   The Phase construction uses the simple add zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L219-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L219-L238

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

theorem Formalism.DoubleCosetMeasures.P.Phase.simple_add_zero {n : ℕ} {y z : Matrix (Fin n) (Fin n) K} (hy : IsUpUni y)
    (hz : IsUpUni z) (hyz : y * z = 1) (j k : Fin n) (hk : (k : ℕ) = j + 1) :
    y j k + z j k = 0 := by sorry
