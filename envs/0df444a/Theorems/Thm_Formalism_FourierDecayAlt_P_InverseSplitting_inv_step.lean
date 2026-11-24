-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseSplitting_inv_step
-- name    : Formalism.FourierDecayAlt.P.InverseSplitting.inv_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:34.163094+00:00
-- url     : https://prove2.me/theorems/2af7be35-eef7-4958-ae54-d0a3d75d40fb
-- title:
--   Inverse Splitting: inv step
-- statement:
--   The Inverse Splitting construction uses the inv step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean#L33-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean#L33-L131

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.InverseSplitting
open C2x2
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseSplitting.inv_step (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) :
    ∀ n, Inv w l n (lsStep w l n).1 (lsStep w l n).2 := by sorry
