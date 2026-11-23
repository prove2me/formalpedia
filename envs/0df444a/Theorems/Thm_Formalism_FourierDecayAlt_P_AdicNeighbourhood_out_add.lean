-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_out_add
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.out_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:30.188456+00:00
-- url     : https://prove2.me/theorems/f3783038-1c66-4b08-b49b-52e336ccf154
-- title:
--   Adic Neighbourhood: out add
-- statement:
--   The Adic Neighbourhood construction uses the out add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L366-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L366-L370

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

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.out_add {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (y : G ⧸ Λ) (v : G) :
    ∃ l ∈ Λ, (Quotient.out (y + (v : G ⧸ Λ)) : G) = Quotient.out y + v + l := by sorry
