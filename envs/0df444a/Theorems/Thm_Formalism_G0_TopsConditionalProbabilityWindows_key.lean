-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_key
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:35.099117+00:00
-- url     : https://prove2.me/theorems/892beb84-643b-4d3e-a29c-78f18caf2d83
-- title:
--   Tops Conditional Probability Windows: key
-- statement:
--   The Tops Conditional Probability Windows construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L159-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L159-L197

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

theorem Formalism.G0.TopsConditionalProbabilityWindows.key (n L K : ℕ) (t : Finset ℕ) (h0t : 0 ∉ t) (h : ¬ CondA n (insert 0 t) L K) :
    ∃ i ∈ range n, ∃ S ∈ powersetCard (if 0 ∈ window n i L then K else K + 1)
      ((window n i L).erase 0), S ⊆ t := by sorry
