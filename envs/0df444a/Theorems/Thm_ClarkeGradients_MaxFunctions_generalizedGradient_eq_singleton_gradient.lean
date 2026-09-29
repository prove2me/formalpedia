-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_generalizedGradient_eq_singleton_gradient
-- name    : ClarkeGradients.MaxFunctions.generalizedGradient_eq_singleton_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:44:18.06888+00:00
-- url     : https://prove2.me/theorems/a46a8b8c-ccc2-4035-8c90-e9aa03e4025e
-- title:
--   (2.3) — ∂ₓg(x̄, u) = {∇f(x̄)} at differentiability points of f, for u ∈ M(x̄)
-- statement:
--   Let $U$ be a nonempty sequentially compact space and let $g:\mathbb R^n\times U\to\mathbb R$ satisfy hypotheses (a)–(d) of Theorem (2.1) (upper semicontinuity of $g$; local Lipschitz continuity in $x$ uniform in $u$; $g'_x=g^\circ_x$ everywhere; upper semicontinuity of $(x,u)\mapsto\partial_x g(x,u)$). Let $f(x)=\max_{u\in U}g(x,u)$ and $M(x)=\{u:\ g(x,u)=f(x)\}$.
--
--   If $f$ is differentiable at a point $\bar x$, then for every $u\in M(\bar x)$
--
--   $$
--   \partial_x g(\bar x,u)=\{\nabla f(\bar x)\}.
--   $$
--
--   At points where the max function is differentiable, every active piece has a one-point generalized gradient equal to $\nabla f(\bar x)$. Combined with (d) and the compactness of $U$, this yields the inclusion $\partial f(x)\subseteq\operatorname{co}\{\partial_x g(x,u):u\in M(x)\}$.
--
--   **Formalization Note** "$\nabla f(\bar x)$ exists" is `DifferentiableAt ℝ f x̄` (Fréchet differentiability), and $\nabla f(\bar x)$ is Mathlib's `gradient`.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 252, proof of Theorem (2.1), Eq. (2.3)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), (2.3), in the proof of Theorem (2.1): under hypotheses (a)–(d),
if `∇f(x̄)` exists then `∂ₓg(x̄, u) = {∇f(x̄)}` for every `u ∈ M(x̄)`.
Here `U` is a nonempty sequentially compact space and
`f = maxFunction g`, `M(x) = maximizers g x`. -/
theorem generalizedGradient_eq_singleton_gradient
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : U) (v : EuclideanSpace ℝ (Fin n)),
      HasOneSidedDirDeriv (fun y => g y u) x v (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : EuclideanSpace ℝ (Fin n) × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) :
    ∀ (xbar : EuclideanSpace ℝ (Fin n)) (u : U),
      DifferentiableAt ℝ (maxFunction g) xbar → u ∈ maximizers g xbar →
        Shared.generalizedGradient (fun y => g y u) xbar = {gradient (maxFunction g) xbar} := by sorry

end ClarkeGradients.MaxFunctions
