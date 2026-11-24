-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_bad_bound
-- name    : Formalism.G0.TopsConditionalProbabilityBounds.bad_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:03.610814+00:00
-- url     : https://prove2.me/theorems/0c39e106-75e0-4998-bcdd-453ae6b538ef
-- title:
--   Tops Conditional Probability Bounds: bad bound
-- statement:
--   The Tops Conditional Probability Bounds construction uses the bad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartC.lean#L101-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartC.lean#L101-L137

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityBounds
open Finset

theorem Formalism.G0.TopsConditionalProbabilityBounds.bad_bound (n : ℕ) (δ : ℝ) (G : ℕ) (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (i : ℕ) (hi : i < n) :
    condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) ≤ (1 - δ) ^ G := by sorry
