-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_diff
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_diff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:20.85514+00:00
-- url     : https://prove2.me/theorems/57aeb770-80b3-4abb-b243-7ced5df0938f
-- title:
--   Inverse Bounded Fixed Point: quad diff
-- statement:
--   The Inverse Bounded Fixed Point construction uses the quad diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L385-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L385-L391

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_diff {Λ : Submodule R K} {G Y Y' : Matrix (Fin m) (Fin m) K} (hG : ∀ i j, G i j ∈ R)
    (hY : ∀ i j, Y i j ∈ R) (hY' : ∀ i j, Y' i j ∈ R) (hd : MemM Λ (Y - Y')) :
    MemM Λ (Y * G * Y - Y' * G * Y') := by sorry
