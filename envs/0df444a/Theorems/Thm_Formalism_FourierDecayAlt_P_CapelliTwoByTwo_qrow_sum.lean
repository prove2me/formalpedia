-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliTwoByTwo_qrow_sum
-- name    : Formalism.FourierDecayAlt.P.CapelliTwoByTwo.qrow_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:02:57.883583+00:00
-- url     : https://prove2.me/theorems/2675a12c-2950-5d83-8d7c-dc6ad7f73621
-- title:
--   Capelli Two By Two: qrow sum
-- statement:
--   The Capelli Two By Two construction uses the qrow sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L153-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L153-L224

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.CapelliTwoByTwo.qrow_sum (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    ∑ d, qrow k r y x Bs j (bvec (posL k r (Fin.last r) d)) * v (posL k r (Fin.last r) d) = qrow k r y x Bs j v := by sorry
