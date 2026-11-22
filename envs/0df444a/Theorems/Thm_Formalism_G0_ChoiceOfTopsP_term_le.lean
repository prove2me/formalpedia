-- Prove2me | Theorems.Thm_Formalism_G0_ChoiceOfTopsP_term_le
-- name    : Formalism.G0.ChoiceOfTopsP.term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:39.462871+00:00
-- url     : https://prove2.me/theorems/aff626f7-973b-4120-95d4-ffed86464a57
-- title:
--   Choice Of Tops P: term le
-- statement:
--   The Choice Of Tops P construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTops.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTops.lean#L16-L23

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTops
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
open Formalism.G0.ChoiceOfTopsP

theorem Formalism.G0.ChoiceOfTopsP.term_le (p a b c d : Prop) {_ : Decidable p} {_ : Decidable a} {_ : Decidable b}
    {_ : Decidable c} {_ : Decidable d} (w : ℝ) (hw : 0 ≤ w) (h : p → a ∨ b ∨ c ∨ d) :
    (if p then w else 0) ≤
      (if a then w else 0) + (if b then w else 0) + (if c then w else 0) + (if d then w else 0) := by sorry
