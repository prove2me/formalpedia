-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_sum_le_prob
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.sum_le_prob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:55.426161+00:00
-- url     : https://prove2.me/theorems/71d81942-ed5d-4194-8473-543c44bd303d
-- title:
--   Tops Choice Probability Lemmas: sum le prob
-- statement:
--   The Tops Choice Probability Lemmas construction uses the sum le prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L162-L173

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.sum_le_prob {S : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ → Prop}
    (Fam : Finset (Finset ℕ)) (hF : ∀ t ∈ Fam, t ⊆ S ∧ A t) :
    ∑ t ∈ Fam, δ ^ t.card * (1 - δ) ^ (S.card - t.card) ≤ P S δ A := by sorry
