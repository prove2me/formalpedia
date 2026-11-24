-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_phi_true
-- name    : Formalism.G0.TopsWeightFunctionBounds.phi_true
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:47.901637+00:00
-- url     : https://prove2.me/theorems/9f202e84-8114-49f6-9f8a-f5f70350c1b5
-- title:
--   Tops Weight Function Bounds: phi true
-- statement:
--   The Tops Weight Function Bounds construction uses the phi true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L259-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L259-L288

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.phi_true (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R)
    (K j d : ℕ) (al ev : Bool) (hj : j < R) :
    Phi R L₂ δ (step R L₂ (.run K j d al ev) true) ≤
      (1 - aF L₂ δ ^ R) ^ (K - 1) *
        (1 - (if (al && okG L₂ j d ev) = true then aF L₂ δ ^ (R - 1 - j) else 0)) := by sorry
