-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_local_zero
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.local_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:36.69945+00:00
-- url     : https://prove2.me/theorems/b7366bf6-5baa-45d7-8c3f-ec46879f26ad
-- title:
--   Adic Neighbourhood: local zero
-- statement:
--   The Adic Neighbourhood construction uses the local zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L379-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L379-L424

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

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.local_zero (Λ N : AddSubgroup K) [Fintype (N ⧸ Λ.addSubgroupOf N)] {d : ℕ}
    (F : (Fin d → K) → ℂ) (hF : LatInvN Λ F) (x : Fin d → K) (hx : Osc N F x) :
    ∑ h : Fin d → N ⧸ Λ.addSubgroupOf N, F (x + fun i => ((Quotient.out (h i) : N) : K)) = 0 := by sorry
