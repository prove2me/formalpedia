-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_smul_def
-- name    : Formalism.ResultantValuation.ParabolicCounting.smul_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:08.769434+00:00
-- url     : https://prove2.me/theorems/02af909f-2451-4337-b050-ebd8fc5cf78a
-- title:
--   Parabolic Counting: smul def
-- statement:
--   The Parabolic Counting construction uses the smul def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean#L36-L37

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

theorem Formalism.ResultantValuation.ParabolicCounting.smul_def (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    g • W = W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F)) := by sorry
