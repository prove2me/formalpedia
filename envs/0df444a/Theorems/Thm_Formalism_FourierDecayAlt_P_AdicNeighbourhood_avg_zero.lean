-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_avg_zero
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.avg_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:22.155675+00:00
-- url     : https://prove2.me/theorems/5c604378-b0cb-4dc9-87c7-c94a224b4727
-- title:
--   Adic Neighbourhood: avg zero
-- statement:
--   The Adic Neighbourhood construction uses the avg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L426-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L426-L466

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

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.avg_zero (Λ N : AddSubgroup K) [Finite (N ⧸ Λ.addSubgroupOf N)] {d : ℕ}
    (F : (Fin d → K) → ℂ) (hF : LatInvN Λ F) (hx : ∀ x, Osc N F x) :
    ∑ᶠ y : Fin d → K ⧸ Λ, F (fun i => Quotient.out (y i)) = 0 := by sorry
