-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_subset
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.window_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:40.35964+00:00
-- url     : https://prove2.me/theorems/bef9c1a7-089c-4c71-a2af-8591d00c85db
-- title:
--   Tops Conditional Probability Windows: window subset
-- statement:
--   The Tops Conditional Probability Windows construction uses the window subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L107-L111

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

theorem Formalism.G0.TopsConditionalProbabilityWindows.window_subset (n i L : ℕ) (hn : 1 ≤ n) : window n i L ⊆ range n := by sorry
