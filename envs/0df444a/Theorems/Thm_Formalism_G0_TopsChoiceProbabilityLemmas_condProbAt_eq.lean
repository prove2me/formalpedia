-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_condProbAt_eq
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.condProbAt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:15.754538+00:00
-- url     : https://prove2.me/theorems/1fa1d47c-22a3-45c6-bd1f-634c738a4ed1
-- title:
--   Tops Choice Probability Lemmas: cond Prob At eq
-- statement:
--   The Tops Choice Probability Lemmas construction uses the cond Prob At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L408-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L408-L428

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
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
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows

theorem Formalism.G0.TopsChoiceProbabilityLemmas.condProbAt_eq (n : ℕ) (δ : ℝ) (i₀ : ℕ) (hi : i₀ < n) (A : Finset ℕ → Prop) :
    condProbAt n δ i₀ A = P ((range n).erase i₀) δ (fun t => A (insert i₀ t)) := by sorry
