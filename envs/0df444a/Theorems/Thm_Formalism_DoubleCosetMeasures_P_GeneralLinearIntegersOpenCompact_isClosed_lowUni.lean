-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_isClosed_lowUni
-- name    : Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.isClosed_lowUni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:26.633048+00:00
-- url     : https://prove2.me/theorems/a08835c2-245b-42c4-95fa-ebb02d53b927
-- title:
--   General Linear Integers Open Compact: is Closed low Uni
-- statement:
--   The General Linear Integers Open Compact construction uses the is Closed low Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L172-L180

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

theorem Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.isClosed_lowUni [T2Space K] (n : ℕ) :
    IsClosed {x : Matrix (Fin n) (Fin n) K | IsLowUni x} := by sorry
