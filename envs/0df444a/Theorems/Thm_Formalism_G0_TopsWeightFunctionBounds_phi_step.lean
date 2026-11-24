-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_phi_step
-- name    : Formalism.G0.TopsWeightFunctionBounds.phi_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:44.942597+00:00
-- url     : https://prove2.me/theorems/23b7a9cf-2fce-4c40-a257-f14a6b6f618c
-- title:
--   Tops Weight Function Bounds: phi step
-- statement:
--   The Tops Weight Function Bounds construction uses the phi step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L290-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L290-L319

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

theorem Formalism.G0.TopsWeightFunctionBounds.phi_step (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R)
    (s : St) (hs : WF R s) :
    δ * Phi R L₂ δ (step R L₂ s true) + (1 - δ) * Phi R L₂ δ (step R L₂ s false) ≤ Phi R L₂ δ s := by sorry
