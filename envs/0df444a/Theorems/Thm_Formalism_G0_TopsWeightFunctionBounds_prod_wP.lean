-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_prod_wP
-- name    : Formalism.G0.TopsWeightFunctionBounds.prod_wP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:59.784851+00:00
-- url     : https://prove2.me/theorems/8c1ac608-d2b3-4288-8a9d-6027ef1584f4
-- title:
--   Tops Weight Function Bounds: prod w P
-- statement:
--   The Tops Weight Function Bounds construction uses the prod w P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L417-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L417-L427

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
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.prod_wP (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range n) :
    ∏ p ∈ Finset.range n, wP δ T p = δ ^ T.card * (1 - δ) ^ (n - T.card) := by sorry
