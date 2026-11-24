-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_standard_lattice_basis_apply
-- name    : Formalism.FourierDecayAlt.P.PBC.Lat.standard_lattice_basis_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:32:22.74411+00:00
-- url     : https://prove2.me/theorems/7f6c8a64-617f-4f48-b1dc-53f92f4fadd0
-- title:
--   Lat: standard lattice basis apply
-- statement:
--   The Lat construction uses the standard lattice basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean#L210-L212

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

theorem Formalism.FourierDecayAlt.P.PBC.Lat.standard_lattice_basis_apply (f : ℕ) (v : Fin f) (β : Bool) :
    b0 f (v, β) = (Pi.single v (if β then Complex.I else 1) : crystallineComparison.V f) := by sorry
