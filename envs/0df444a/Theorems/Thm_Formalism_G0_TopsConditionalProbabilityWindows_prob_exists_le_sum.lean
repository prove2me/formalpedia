-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_exists_le_sum
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.prob_exists_le_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:49.573972+00:00
-- url     : https://prove2.me/theorems/d8fcffb5-ee4e-4577-9633-cf1582442731
-- title:
--   Tops Conditional Probability Windows: prob exists le sum
-- statement:
--   The Tops Conditional Probability Windows construction uses the prob exists le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L55-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L55-L76

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityWindows

theorem Formalism.G0.TopsConditionalProbabilityWindows.prob_exists_le_sum {ι : Type*} {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (s : Finset ι)
    (A : ι → Finset ℕ → Prop) :
    P U δ (fun t => ∃ j ∈ s, A j t) ≤ ∑ j ∈ s, P U δ (A j) := by sorry
