-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_partA
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.partA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:49.282802+00:00
-- url     : https://prove2.me/theorems/a0e8e4d4-2d9a-49d1-8b63-87bbbfb53b0e
-- title:
--   Tops Choice Probability Lemmas: part A
-- statement:
--   The Tops Choice Probability Lemmas construction uses the part A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L444-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L444-L481

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.partA (n : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (L₂ K i₀ : ℕ) (hn : 1 ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) ≤
      n * (L₂.choose K : ℝ) * δ ^ K := by sorry
