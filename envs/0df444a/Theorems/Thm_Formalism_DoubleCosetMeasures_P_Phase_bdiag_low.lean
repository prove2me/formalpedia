-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_bdiag_low
-- name    : Formalism.DoubleCosetMeasures.P.Phase.bdiag_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:45.056326+00:00
-- url     : https://prove2.me/theorems/b55d249c-756a-444a-b91b-f22d70dc8b72
-- title:
--   Phase: bdiag low
-- statement:
--   The Phase construction uses the bdiag low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L423-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L423-L434

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

theorem Formalism.DoubleCosetMeasures.P.Phase.bdiag_low (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x) :
    IsLowUni (bdiag s x) := by sorry
