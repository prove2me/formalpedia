-- Prove2me | Theorems.Thm_CondatPD_FB_lemma_4_5
-- name    : CondatPD.FB.lemma_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:40:04.624923+00:00
-- url     : https://prove2.me/theorems/1b074b71-d061-46f5-8ff0-d06434388d59
-- title:
--   Lemma 4.5 — Baillon–Haddad theorem
-- statement:
--   Let $J$ be convex and differentiable on a real Hilbert space, and let $\kappa>0$. If the scaled gradient $\kappa\nabla J$ is nonexpansive, then the gradient is $\kappa$-cocoercive:
--   $$\kappa\|\nabla J(x)-\nabla J(y)\|^2\le\langle\nabla J(x)-\nabla J(y),x-y\rangle\quad\text{for all }x,y.$$
--
--   This connects the smoothness estimate to the forward–backward hypothesis on the gradient.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 9, Lemma 4.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

open InnerProductSpace

namespace CondatPD.FB

/-- Lemma 4.5, p. 9: Baillon–Haddad cocoercivity. -/
theorem lemma_4_5 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (J : K → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ Set.univ J) (hdiff : Differentiable ℝ J) (hκ : 0 < κ)
    (hlip : ThreeOpSplitting.Convergence.IsNonexpansive (fun x => κ • gradient J x)) :
    ThreeOpSplitting.Convergence.IsCocoercive κ (gradient J) := by sorry

end CondatPD.FB
