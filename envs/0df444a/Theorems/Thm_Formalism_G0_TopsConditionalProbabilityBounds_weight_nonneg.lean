-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_weight_nonneg
-- name    : Formalism.G0.TopsConditionalProbabilityBounds.weight_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:30.753219+00:00
-- url     : https://prove2.me/theorems/750c517d-f2c6-4298-80ec-d74c540f4eef
-- title:
--   Tops Conditional Probability Bounds: weight nonneg
-- statement:
--   The Tops Conditional Probability Bounds construction uses the weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartC.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartC.lean#L11-L13

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

theorem Formalism.G0.TopsConditionalProbabilityBounds.weight_nonneg (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (T : Finset ℕ) :
    0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) := by sorry
