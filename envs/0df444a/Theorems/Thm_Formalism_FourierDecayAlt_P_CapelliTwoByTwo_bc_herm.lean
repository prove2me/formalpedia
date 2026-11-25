-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliTwoByTwo_bc_herm
-- name    : Formalism.FourierDecayAlt.P.CapelliTwoByTwo.bc_herm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:36.536474+00:00
-- url     : https://prove2.me/theorems/64c856db-5cb3-4a22-9e43-8837f0e40245
-- title:
--   Capelli Two By Two: bc herm
-- statement:
--   The Capelli Two By Two construction uses the bc herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L226-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L226-L235

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

theorem Formalism.FourierDecayAlt.P.CapelliTwoByTwo.bc_herm {y x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [y, x] Bs) (j : Fin (mdim k r (Fin.last r))) (w : Fin (2 * r + k + 1) → ℂ) (hw : w ∈ [y, x]) :
    herm (Hpk k r) (bc k r y x Bs j) w =
      if j.val = 0 then herm (Hpk k r) y w else if j.val = 1 then herm (Hpk k r) x w else 0 := by sorry
