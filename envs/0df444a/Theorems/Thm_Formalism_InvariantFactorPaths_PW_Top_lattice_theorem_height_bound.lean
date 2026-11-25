-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_lattice_theorem_height_bound
-- name    : Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:10.012297+00:00
-- url     : https://prove2.me/theorems/f0b786b4-0b10-4855-82a1-d3ed9fcab6a2
-- title:
--   Top: lattice theorem height bound
-- statement:
--   The Top construction uses the lattice theorem height bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/FinalM.lean#L7-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/FinalM.lean#L7-L7

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeTheoremOfDischarge
import Definitions.Def_Formalism_PolynomialDimension_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.PW.Top

theorem Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound : LatticeTheoremHeightBound := by sorry
