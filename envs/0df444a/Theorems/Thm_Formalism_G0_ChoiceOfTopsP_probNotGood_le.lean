-- Prove2me | Theorems.Thm_Formalism_G0_ChoiceOfTopsP_probNotGood_le
-- name    : Formalism.G0.ChoiceOfTopsP.probNotGood_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:43.836175+00:00
-- url     : https://prove2.me/theorems/2c738176-b797-42d7-8aac-56335b692900
-- title:
--   Choice Of Tops P: prob Not Good le
-- statement:
--   The Choice Of Tops P construction uses the prob Not Good le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTops.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTops.lean#L25-L44

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

theorem Formalism.G0.ChoiceOfTopsP.probNotGood_le (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    probNotGood n δ L₂ K r N₁ G ≤
      condProb n δ (fun T => ¬ CondA n T L₂ K) +
      condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) +
      condProb n δ (fun T => ¬ CondC n T G) +
      condProb n δ (fun T => T.card < N₁) := by sorry
