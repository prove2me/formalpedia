-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_dual_sep
-- name    : Formalism.FourierDecayAlt.P.PBC.Lat.dual_sep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:31:46.046256+00:00
-- url     : https://prove2.me/theorems/714716ba-d065-4bf5-ace6-f3717b95560d
-- title:
--   Lat: dual sep
-- statement:
--   The Lat construction uses the dual sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean#L317-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean#L317-L333

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.PBC.Lat

theorem Formalism.FourierDecayAlt.P.PBC.Lat.dual_sep (f : ℕ) (R : ℝ) (hR : 0 < R) (σ σ' : crystallineComparison.V f) (hσ : σ ∈ crystallineComparison.dualSet (Lstd f R))
    (hσ' : σ' ∈ crystallineComparison.dualSet (Lstd f R)) (hne : σ ≠ σ') : 1 / (2 * R) ≤ ‖σ - σ'‖ := by sorry
