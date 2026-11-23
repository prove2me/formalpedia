-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Near_prod
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.Near.prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:04.945462+00:00
-- url     : https://prove2.me/theorems/d73a895d-55c6-4215-a2b3-691aa8f96b48
-- title:
--   Near: prod
-- statement:
--   The Near construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L227-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L227-L234

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
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.Near.prod {ι : Type} {a : K} (ha : a ∈ R) (S : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ S, Near R a (f i)) : Near R a (∏ i ∈ S, f i) := by sorry
