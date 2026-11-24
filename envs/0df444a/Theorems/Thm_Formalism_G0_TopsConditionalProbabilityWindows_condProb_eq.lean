-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_condProb_eq
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.condProb_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:09.688818+00:00
-- url     : https://prove2.me/theorems/a5c902e1-8046-40ec-b7ce-774530b94371
-- title:
--   Tops Conditional Probability Windows: cond Prob eq
-- statement:
--   The Tops Conditional Probability Windows construction uses the cond Prob eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L16-L36

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

theorem Formalism.G0.TopsConditionalProbabilityWindows.condProb_eq (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (A : Finset ℕ → Prop) :
    condProb n δ A = P ((range n).erase 0) δ (fun t => A (insert 0 t)) := by sorry
