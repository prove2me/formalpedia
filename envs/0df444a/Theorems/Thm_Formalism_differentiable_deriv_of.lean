-- Prove2me | Theorems.Thm_Formalism_differentiable_deriv_of
-- name    : Formalism.differentiable_deriv_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:41.387822+00:00
-- url     : https://prove2.me/theorems/d18742a5-d1ee-4d00-8b2e-0be103736a00
-- title:
--   Formalism: differentiable deriv of
-- statement:
--   The Formalism construction uses the differentiable deriv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L84-L85

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

theorem Formalism.differentiable_deriv_of {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) := by sorry
