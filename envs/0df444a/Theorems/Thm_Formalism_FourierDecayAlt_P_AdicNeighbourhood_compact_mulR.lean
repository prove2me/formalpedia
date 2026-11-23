-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_compact_mulR
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.compact_mulR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:34.691803+00:00
-- url     : https://prove2.me/theorems/54ba20e8-ba11-4a5c-b113-8d39f75f15bd
-- title:
--   Adic Neighbourhood: compact mul R
-- statement:
--   The Adic Neighbourhood construction uses the compact mul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L486-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L486-L490

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
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.compact_mulR [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
    (hc : IsCompact (R : Set K)) (ν : K) : IsCompact ((mulR R ν : AddSubgroup K) : Set K) := by sorry
