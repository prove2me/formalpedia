-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_bound
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.window_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:08:01.777338+00:00
-- url     : https://prove2.me/theorems/86072c29-fd43-4e0f-b800-179d00708e56
-- title:
--   Tops Conditional Probability Windows: window bound
-- statement:
--   The Tops Conditional Probability Windows construction uses the window bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L117-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L117-L157

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

theorem Formalism.G0.TopsConditionalProbabilityWindows.window_bound (δ : ℝ) (h0 : 0 ≤ δ) (L K : ℕ) (hLδ : (L : ℝ) * δ ≤ 1) (W : Finset ℕ)
    (hW : W.card ≤ L) :
    ∑ S ∈ powersetCard (if 0 ∈ W then K else K + 1) (W.erase 0), δ ^ S.card
      ≤ (L.choose K : ℝ) * δ ^ K := by sorry
