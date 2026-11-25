-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliTwoByTwo_bc_inWb
-- name    : Formalism.FourierDecayAlt.P.CapelliTwoByTwo.bc_inWb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:51:41.752848+00:00
-- url     : https://prove2.me/theorems/5fc16a88-a530-441e-9ea7-59f9c5579a3e
-- title:
--   Capelli Two By Two: bc in Wb
-- statement:
--   The Capelli Two By Two construction uses the bc in Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L145-L151

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

theorem Formalism.FourierDecayAlt.P.CapelliTwoByTwo.bc_inWb {y x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y)
    (hx : inWb k r x) (hB : ∀ a, inWb k r (Bs a)) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bc k r y x Bs j) := by sorry
