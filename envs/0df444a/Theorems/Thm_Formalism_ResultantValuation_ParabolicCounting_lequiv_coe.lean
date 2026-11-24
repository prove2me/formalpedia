-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_lequiv_coe
-- name    : Formalism.ResultantValuation.ParabolicCounting.lequiv_coe
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:12.348104+00:00
-- url     : https://prove2.me/theorems/1ee8ba48-a726-4c65-84fa-4f240f1efdc9
-- title:
--   Parabolic Counting: lequiv coe
-- statement:
--   The Parabolic Counting construction uses the lequiv coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L42-L47

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

theorem Formalism.ResultantValuation.ParabolicCounting.lequiv_coe (g : GL (Fin (r + t)) F) :
    ((lequiv F r t g : (Fin (r + t) → F) ≃ₗ[F] (Fin (r + t) → F)) :
        (Fin (r + t) → F) →ₗ[F] (Fin (r + t) → F)) =
      Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F) := by sorry
