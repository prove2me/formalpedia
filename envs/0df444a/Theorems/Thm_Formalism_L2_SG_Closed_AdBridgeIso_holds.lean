-- Prove2me | Theorems.Thm_Formalism_L2_SG_Closed_AdBridgeIso_holds
-- name    : Formalism.L2.SG.Closed.AdBridgeIso_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:48.315155+00:00
-- url     : https://prove2.me/theorems/8d038f77-1c25-5792-b7dc-e661c42cad55
-- title:
--   Closed: Ad Bridge Iso holds
-- statement:
--   The Closed construction uses the Ad Bridge Iso holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedVolumeStatements/AdelicIsomorphismStatement.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedVolumeStatements/AdelicIsomorphismStatement.lean#L14-L15

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_JRMapTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_ExistsNotMemRange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_ContinuousOfHAInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFinInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BridgeMaxCpt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BridgeRatPts
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedVolumeStatements_AdelicIsomorphismStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Closed

theorem Formalism.L2.SG.Closed.AdBridgeIso_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeIso I := by sorry
