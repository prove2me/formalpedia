-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mfac_shift0
-- name    : Formalism.FourierDecayAlt.P.PBC.Lat.mfac_shift0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:32:37.949372+00:00
-- url     : https://prove2.me/theorems/b3460f0f-42e9-423f-a3e5-6e1f779615c0
-- title:
--   Lat: mfac shift0
-- statement:
--   The Lat construction uses the mfac shift0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean#L284-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean#L284-L299

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

theorem Formalism.FourierDecayAlt.P.PBC.Lat.mfac_shift0 (K : ℕ) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    crystallineComparison.mfac K L a ≤ crystallineComparison.mfac K (L + δ) (a + δ) := by sorry
