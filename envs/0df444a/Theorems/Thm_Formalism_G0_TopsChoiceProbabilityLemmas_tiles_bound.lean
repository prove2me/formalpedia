-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_tiles_bound
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.tiles_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:08.091993+00:00
-- url     : https://prove2.me/theorems/d1f9c672-722f-4b6c-8530-d2fc3d21acb0
-- title:
--   Tops Choice Probability Lemmas: tiles bound
-- statement:
--   The Tops Choice Probability Lemmas construction uses the tiles bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L511-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L511-L557

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.tiles_bound {n : ℕ} {δ : ℝ} {r u M₀ i₀ : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) (s₀ : ℕ) (hs₀ : s₀ < n / ((6 * r + 1) * u)) :
    P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
      ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) ≤
      (1 - markedBound δ r u) ^ M₀ := by sorry
