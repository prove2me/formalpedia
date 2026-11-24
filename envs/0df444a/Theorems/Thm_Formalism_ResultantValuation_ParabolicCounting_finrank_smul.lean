-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_finrank_smul
-- name    : Formalism.ResultantValuation.ParabolicCounting.finrank_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:11.977571+00:00
-- url     : https://prove2.me/theorems/487ec73a-3f90-425c-a70c-4b7558c050f6
-- title:
--   Parabolic Counting: finrank smul
-- statement:
--   The Parabolic Counting construction uses the finrank smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L49-L51

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ResultantValuation
open Module
open Formalism.ResultantValuation.ParabolicCounting
variable (F : Type) [Field F] (r t : ℕ)
attribute [local instance] act

theorem Formalism.ResultantValuation.ParabolicCounting.finrank_smul (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    finrank F (g • W : Submodule F (Fin (r + t) → F)) = finrank F W := by sorry
