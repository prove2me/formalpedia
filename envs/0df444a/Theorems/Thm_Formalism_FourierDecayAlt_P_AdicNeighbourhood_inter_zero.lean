-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_inter_zero
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.inter_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:33.012137+00:00
-- url     : https://prove2.me/theorems/597bc51e-2500-4979-9f9c-c30c27cc015d
-- title:
--   Adic Neighbourhood: inter zero
-- statement:
--   The Adic Neighbourhood construction uses the inter zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L46-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L46-L80

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

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.inter_zero {R : Subring K} [T2Space K] [IsReduced K] (hc : IsCompact (R : Set K))
    (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (ϖ : K) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R)
    (x : K) (hx : ∀ n, x ∈ I R (ϖ ^ n)) : x = 0 := by sorry
