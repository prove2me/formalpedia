-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_G_differentiableOn
-- name    : Formalism.FX.LFunctionPartialSum.G_differentiableOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:14.324814+00:00
-- url     : https://prove2.me/theorems/acf314e6-ab25-4e79-9f04-053a161257ab
-- title:
--   LFunction Partial Sum: G differentiable On
-- statement:
--   The LFunction Partial Sum construction uses the G differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L141-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L141-L181

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.FX.LFunctionPartialSum.G_differentiableOn {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) :
    DifferentiableOn ℂ (G χ) {s : ℂ | 0 < s.re} := by sorry
