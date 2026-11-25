-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_partB
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.partB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:17.055436+00:00
-- url     : https://prove2.me/theorems/133ff95d-927e-48bd-890b-02a02b34b320
-- title:
--   Tops Choice Probability Lemmas: part B
-- statement:
--   The Tops Choice Probability Lemmas construction uses the part B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L559-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L559-L585

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.partB {n : ℕ} {δ : ℝ} {r u M₀ i₀ : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀) ≤
      n * (1 - markedBound δ r u) ^ M₀ := by sorry
