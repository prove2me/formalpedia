-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_I_compact
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.I_compact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:22.062024+00:00
-- url     : https://prove2.me/theorems/1a06dcf8-4813-4bf9-9269-5bc0eabd9280
-- title:
--   Adic Neighbourhood: I compact
-- statement:
--   The Adic Neighbourhood construction uses the I compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L25-L31

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.I_compact {R : Subring K} (hc : IsCompact (R : Set K)) (a : K) : IsCompact (I R a) := by sorry
