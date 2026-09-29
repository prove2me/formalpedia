-- Prove2me | Theorems.Thm_DifferentiableAt_comp_ofReal
-- name    : DifferentiableAt.comp_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:26:08.194576+00:00
-- url     : https://prove2.me/theorems/01f5814b-afd7-4a77-a368-20d085185f14
-- title:
--   Restricting a complex-differentiable function to the real line preserves differentiability
-- statement:
--   Let $e : \mathbb{C} \to \mathbb{C}$ be a function and let $z \in \mathbb{R}$. If $e$ is complex-differentiable at the point $z$ (viewed inside $\mathbb{C}$), then the restriction of $e$ to the real line,
--   $$x \mapsto e(x), \qquad x \in \mathbb{R},$$
--   is differentiable over $\mathbb{R}$ at $z$:
--   $$\text{DifferentiableAt}_{\mathbb{C}}\, e \; z \implies \text{DifferentiableAt}_{\mathbb{R}}\, (x \mapsto e(x)) \; z.$$
--
--   This is the composition of $e$ with the smooth embedding $\mathbb{R} \hookrightarrow \mathbb{C}$, together with restriction of scalars from $\mathbb{C}$ to $\mathbb{R}$.
--
--   In the PNT+ project this lemma is used whenever a holomorphic function (such as $\zeta$, $\zeta'/\zeta$, or a Mellin transform) is evaluated along a horizontal line in the complex plane and must be differentiated as a function of the real parameter, e.g. when computing or estimating contour integrals leg by leg.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L30-L32

/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
### Auxiliary lemmas
-/

open Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

theorem DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z := by sorry
