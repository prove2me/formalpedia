-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_partC
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.partC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:41.808473+00:00
-- url     : https://prove2.me/theorems/b36a6ff4-d741-4f96-aa67-e1516a75679f
-- title:
--   Tops Choice Probability Lemmas: part C
-- statement:
--   The Tops Choice Probability Lemmas construction uses the part C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L483-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L483-L509

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.partC (n : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (G' N₁ i₀ : ℕ) (hn : 1 ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁) ≤
      n * binUpper G' δ (N₁ - 1) := by sorry
