-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_isClosed_upUni
-- name    : Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.isClosed_upUni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:50.340003+00:00
-- url     : https://prove2.me/theorems/f85011b5-a676-40a3-83e0-6e59688b0647
-- title:
--   General Linear Integers Open Compact: is Closed up Uni
-- statement:
--   The General Linear Integers Open Compact construction uses the is Closed up Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L162-L170

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

theorem Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.isClosed_upUni [T2Space K] (n : ℕ) :
    IsClosed {x : Matrix (Fin n) (Fin n) K | IsUpUni x} := by sorry
