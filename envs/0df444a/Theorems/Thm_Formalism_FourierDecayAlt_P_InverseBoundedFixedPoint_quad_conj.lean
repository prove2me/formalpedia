-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_conj
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:05.845808+00:00
-- url     : https://prove2.me/theorems/8f2fdee1-6d33-48f2-8051-9aac88acbfba
-- title:
--   Inverse Bounded Fixed Point: quad conj
-- statement:
--   The Inverse Bounded Fixed Point construction uses the quad conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L722-L725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L722-L725

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
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_conj (P H : Matrix (Fin m) (Fin m) K) (v : Fin m → K) :
    (P *ᵥ v) ⬝ᵥ (H *ᵥ (P *ᵥ v)) = v ⬝ᵥ ((Pᵀ * H * P) *ᵥ v) := by sorry
