-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_unitBox_isCompact
-- name    : Formalism.FourierDecayAlt.P.A6x5.unitBox_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:15.494678+00:00
-- url     : https://prove2.me/theorems/3428abdf-b4ef-4727-87b3-2088bf4a04fb
-- title:
--   A6x5: unit Box is Compact
-- statement:
--   The A6x5 construction uses the unit Box is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L203-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L203-L221

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x5.unitBox_isCompact (hD : LocalDatum K R ψ) (ϖ : Kˣ) (j : ℕ) :
    IsCompact (unitBox R ϖ j) := by sorry
