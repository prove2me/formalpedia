-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_inv_mul_uh
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.inv_mul_uh
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:51:02.305587+00:00
-- url     : https://prove2.me/theorems/4aaf4cee-754a-58cd-9b05-dd491846e774
-- title:
--   Frame Entries: inv mul uh
-- statement:
--   The Frame Entries construction uses the inv mul uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L109-L109

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_inv_mul_uh

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

theorem Formalism.FourierDecayAlt.P.FrameEntries.inv_mul_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by sorry
