-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_identity
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:51.727852+00:00
-- url     : https://prove2.me/theorems/165a4f11-15b0-4a8e-b20a-8ad82fa0cd76
-- title:
--   Inverse Bounded Fixed Point: quad identity
-- statement:
--   The Inverse Bounded Fixed Point construction uses the quad identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L575-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L575-L577

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_identity (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) :
    y ⬝ᵥ (MW w *ᵥ y) = 2 * (∑ k, y k + ∏ k, w k - 1) := by sorry
