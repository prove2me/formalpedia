-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_regular_smooth
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.regular_smooth
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:31:16.963743+00:00
-- url     : https://prove2.me/theorems/269a9b9b-e6fe-4644-9b27-bede923c135a
-- title:
--   Frame Entries: regular smooth
-- statement:
--   The Frame Entries construction uses the regular smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L314-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L314-L326

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
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
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FrameEntries.regular_smooth {f : Mx k r → ℂ} (hf : IsRegular k r f) (i : Fin (r + 1)) (D : Set (Mx k r)) :
    SmoothLev k r i D f := by sorry
