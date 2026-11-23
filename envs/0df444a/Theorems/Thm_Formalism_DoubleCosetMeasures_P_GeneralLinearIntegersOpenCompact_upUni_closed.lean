-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_upUni_closed
-- name    : Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.upUni_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:47.419792+00:00
-- url     : https://prove2.me/theorems/53acad0e-6ce4-4ccc-bbfc-f467c6032866
-- title:
--   General Linear Integers Open Compact: up Uni closed
-- statement:
--   The General Linear Integers Open Compact construction uses the up Uni closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L236-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L236-L237

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
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

theorem Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.upUni_closed [T2Space K] (n : ℕ) : IsClosed (upUniG K n : Set (GL (Fin n) K)) := by sorry
