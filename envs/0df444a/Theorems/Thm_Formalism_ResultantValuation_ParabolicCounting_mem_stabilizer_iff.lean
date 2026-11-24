-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_mem_stabilizer_iff
-- name    : Formalism.ResultantValuation.ParabolicCounting.mem_stabilizer_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:06.208404+00:00
-- url     : https://prove2.me/theorems/75ddcde6-d790-4b1d-911e-0794089bce89
-- title:
--   Parabolic Counting: mem stabilizer iff
-- statement:
--   The Parabolic Counting construction uses the mem stabilizer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L53-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L53-L82

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

theorem Formalism.ResultantValuation.ParabolicCounting.mem_stabilizer_iff (g : GL (Fin (r + t)) F) :
    g ∈ MulAction.stabilizer (GL (Fin (r + t)) F) (firstBlock F r t) ↔
      g ∈ parabolicSet F r t := by sorry
