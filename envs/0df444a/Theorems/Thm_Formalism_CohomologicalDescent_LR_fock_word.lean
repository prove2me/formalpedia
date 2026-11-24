-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_fock_word
-- name    : Formalism.CohomologicalDescent.LR.fock_word
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:03.774579+00:00
-- url     : https://prove2.me/theorems/053e721d-74b1-4946-89ce-37c43143bd3c
-- title:
--   LR: fock word
-- statement:
--   The LR construction uses the fock word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L164-L169

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LR.fock_word (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin r × Fin r) ℚ)
    (hF : F ∈ dualWeyl ℚ r r ν) (w : List (Fin r × Fin r × ℕ)) :
    fockQ F (applyWord ℚ w (hw ℚ le_rfl ν)) =
      eval (idFrame ℚ r r) (applyWord ℚ (transposeWord w) F) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by sorry
