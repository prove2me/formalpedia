-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_expand
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:43.887953+00:00
-- url     : https://prove2.me/theorems/0909eb84-23d8-4cc7-bda9-3e00bcaea23c
-- title:
--   Inverse Bounded Fixed Point: quad expand
-- statement:
--   The Inverse Bounded Fixed Point construction uses the quad expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L522-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L522-L537

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_expand (y w : Fin m → K) :
    y ⬝ᵥ (MW w *ᵥ y) = 2 * (∑ i, y i ^ 2 * w i +
      ∑ i, ∑ j, if j < i then y i * uW w i j * y j else 0) := by sorry
