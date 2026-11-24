-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prod_g
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prod_g
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:59.680808+00:00
-- url     : https://prove2.me/theorems/2f0212c4-d9fb-4817-9da5-b49fd5064178
-- title:
--   Tops Choice Probability Lemmas: prod g
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prod g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L328-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L328-L340

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prod_g (X Y : ℝ) (m : ℕ) :
    ∏ c ∈ Icc 1 (2 * m + 1), (if Odd c then X else Y) = X ^ (m + 1) * Y ^ m := by sorry
