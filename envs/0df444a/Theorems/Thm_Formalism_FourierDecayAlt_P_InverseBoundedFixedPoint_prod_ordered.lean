-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_prod_ordered
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.prod_ordered
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:49.637956+00:00
-- url     : https://prove2.me/theorems/f790b2df-6886-4ee0-89ce-2a22ab92cc9d
-- title:
--   Inverse Bounded Fixed Point: prod ordered
-- statement:
--   The Inverse Bounded Fixed Point construction uses the prod ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L539-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L539-L543

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.prod_ordered (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) (s : Finset (Fin m)) :
    ∏ i ∈ s, w i = 1 - ∑ i ∈ s, (y i * w i) * ∏ j ∈ s.filter (· < i), w j := by sorry
