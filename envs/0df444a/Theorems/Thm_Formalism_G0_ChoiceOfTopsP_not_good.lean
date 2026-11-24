-- Prove2me | Theorems.Thm_Formalism_G0_ChoiceOfTopsP_not_good
-- name    : Formalism.G0.ChoiceOfTopsP.not_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:47.017461+00:00
-- url     : https://prove2.me/theorems/b7442fe0-c336-412e-b042-9e135b2bea2d
-- title:
--   Choice Of Tops P: not good
-- statement:
--   The Choice Of Tops P construction uses the not good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTops.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTops.lean#L9-L14

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

theorem Formalism.G0.ChoiceOfTopsP.not_good {n : ℕ} {T : Finset ℕ} {L₂ K r N₁ G : ℕ} (h : ¬ GoodOrbit n T L₂ K r N₁ G) :
    ¬ CondA n T L₂ K ∨ (¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ∨ ¬ CondC n T G ∨ T.card < N₁ := by sorry
