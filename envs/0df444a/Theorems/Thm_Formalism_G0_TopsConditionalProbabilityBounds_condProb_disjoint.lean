-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_condProb_disjoint
-- name    : Formalism.G0.TopsConditionalProbabilityBounds.condProb_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:05.015919+00:00
-- url     : https://prove2.me/theorems/5d70bd5e-0e56-40be-bd87-e96128529533
-- title:
--   Tops Conditional Probability Bounds: cond Prob disjoint
-- statement:
--   The Tops Conditional Probability Bounds construction uses the cond Prob disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartC.lean#L27-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartC.lean#L27-L99

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

theorem Formalism.G0.TopsConditionalProbabilityBounds.condProb_disjoint (n : ℕ) (δ : ℝ) (S : Finset ℕ) (hS : S ⊆ range n) (h0 : 0 ∉ S)
    (hn : 1 ≤ n) :
    condProb n δ (fun T => Disjoint S T) = (1 - δ) ^ S.card := by sorry
