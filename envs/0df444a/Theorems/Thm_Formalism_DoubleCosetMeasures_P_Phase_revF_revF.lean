-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
-- name    : Formalism.DoubleCosetMeasures.P.Phase.revF_revF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:13:37.996821+00:00
-- url     : https://prove2.me/theorems/30999a4d-86f7-4efd-8c6c-72445674aad9
-- title:
--   Phase: rev F rev F
-- statement:
--   The Phase construction uses the rev F rev F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L89-L89

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

theorem Formalism.DoubleCosetMeasures.P.Phase.revF_revF (s : List ℕ) (a : Fin s.sum) : revF s (revF s a) = a := by sorry
