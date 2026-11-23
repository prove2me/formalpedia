-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_glR_open
-- name    : Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:52.40547+00:00
-- url     : https://prove2.me/theorems/9f0b70a1-cdfa-4927-9c4d-fcdff190ba2d
-- title:
--   General Linear Integers Open Compact: gl R open
-- statement:
--   The General Linear Integers Open Compact construction uses the gl R open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L141-L143

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
import Theorems.Thm_UpperTheory_Reformulated_B_GLRealOpen_glR_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen (glR R n : Set (GL (Fin n) K)) := by sorry
