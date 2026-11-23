-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_phase_identity
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.phase_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:46.770801+00:00
-- url     : https://prove2.me/theorems/4a60fd34-a767-453f-9d16-287dfb7199d3
-- title:
--   Inverse Bounded Fixed Point: phase identity
-- statement:
--   The Inverse Bounded Fixed Point construction uses the phase identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L545-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L545-L573

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.phase_identity (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) :
    ∑ k, y k + ∏ k, w k - 1 = ∑ i, y i ^ 2 * w i +
      ∑ i, ∑ j, if j < i then y i * uW w i j * y j else 0 := by sorry
