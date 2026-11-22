-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_marginal
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prob_marginal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:41.143601+00:00
-- url     : https://prove2.me/theorems/437c8236-e4f3-491d-9db7-8400199a5a42
-- title:
--   Tops Choice Probability Lemmas: prob marginal
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prob marginal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L83-L88

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prob_marginal {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) (A : Finset ℕ → Prop) :
    P U δ (fun t => A (t ∩ S)) = P S δ A := by sorry
