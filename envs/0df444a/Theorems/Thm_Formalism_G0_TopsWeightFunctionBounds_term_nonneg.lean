-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_term_nonneg
-- name    : Formalism.G0.TopsWeightFunctionBounds.term_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:13.477187+00:00
-- url     : https://prove2.me/theorems/dbb9c7a7-b22c-4685-9570-84de5d720107
-- title:
--   Tops Weight Function Bounds: term nonneg
-- statement:
--   The Tops Weight Function Bounds construction uses the term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L815-L819
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L815-L819

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds

theorem Formalism.G0.TopsWeightFunctionBounds.term_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (P : Prop) [Decidable P] (T : Finset ℕ) (n : ℕ) :
    0 ≤ (if P then ∏ p ∈ Finset.range n, wP δ T p else 0) := by sorry
