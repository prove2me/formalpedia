-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_finite_quot
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.finite_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:17.412906+00:00
-- url     : https://prove2.me/theorems/fd467cd3-54b6-42e5-9e11-35bb4055a36e
-- title:
--   Adic Neighbourhood: finite quot
-- statement:
--   The Adic Neighbourhood construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L468-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L468-L471

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

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.finite_quot [TopologicalSpace K] [IsTopologicalRing K] (N Λ : AddSubgroup K)
    (hN : IsCompact (N : Set K)) (hΛ : IsOpen (Λ : Set K)) : Finite (N ⧸ Λ.addSubgroupOf N) := by sorry
