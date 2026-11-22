-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_w_nonneg
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.w_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:44.195842+00:00
-- url     : https://prove2.me/theorems/e6aae4a4-9897-440a-8af2-aeb62c6410d8
-- title:
--   Tops Conditional Probability Windows: w nonneg
-- statement:
--   The Tops Conditional Probability Windows construction uses the w nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L38-L40

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

theorem Formalism.G0.TopsConditionalProbabilityWindows.w_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a b : ℕ) : 0 ≤ δ ^ a * (1 - δ) ^ b := by sorry
