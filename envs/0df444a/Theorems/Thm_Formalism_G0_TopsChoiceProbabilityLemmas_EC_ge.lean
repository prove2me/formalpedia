-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_EC_ge
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.EC_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:43.450808+00:00
-- url     : https://prove2.me/theorems/16beb979-7d49-4e96-adc0-a30e47a6725e
-- title:
--   Tops Choice Probability Lemmas: EC ge
-- statement:
--   The Tops Choice Probability Lemmas construction uses the EC ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L342-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L342-L372

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.EC_ge {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {r u s c : ℕ} (hc : 1 ≤ c)
    (hU : cell r u s c ⊆ U) :
    (if Odd c then (1 - δ) ^ u else ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) ≤
      P U δ (EC r u s c) := by sorry
