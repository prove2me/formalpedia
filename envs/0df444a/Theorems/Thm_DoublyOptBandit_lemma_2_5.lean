-- Prove2me | Theorems.Thm_DoublyOptBandit_lemma_2_5
-- name    : DoublyOptBandit.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:26:53.462222+00:00
-- url     : https://prove2.me/theorems/885313bd-249e-44e0-8f9e-a4af79f1e544
-- title:
--   Lemma 2.5 — a small Newton decrement localizes the minimizer: $\|x-x^\star\|_x\le2\lambda(x,g)$
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex and let $g$ be a self-concordant function on $\operatorname{int}X$ that tends to $+\infty$ at the boundary of $X$. Let $x\in\operatorname{int}X$ with $\nabla^2g(x)$ positive definite, and let the Newton decrement $\lambda(x,g)=\|\nabla g(x)\|_{x,\star}$ satisfy $\lambda(x,g)\le\frac12$. Then $g$ attains its minimum over $\operatorname{int}X$, and every minimizer $x^\star$ satisfies
--   $$
--   \|x-x^\star\|_x\le 2\lambda(x,g),
--   $$
--   where $\|h\|_x=\sqrt{h^\top\nabla^2g(x)h}$ is the local norm of $g$ at $x$.
--
--   In the analysis of the mirror descent step this bounds the distance between consecutive iterates in the local norm of the barrier.
--
--   Differences from the source:
--   - encoding: a self-concordant function g → ConvexOptimization.IsSelfConcordantOn (int X) g together with g → +∞ at every boundary point of X (IsBarrier X g); reason: the closed self-concordant functions of the cited theory, of which the paper's g = R + quadratic (Appendix A) is one; Definition 2.1 without the ν-inequality
--   - encoding: λ(x, g) and ‖·‖ₓ,⋆ defined by (∇²g(x))⁻¹ → ∇²g(x) assumed positive definite; reason: the dual norm is defined only for a nonsingular Hessian (p.5, non-degeneracy); excludes only undefined cases
--   - reading: ‖x − argmin_{x′∈X} g(x′)‖ₓ ≤ 2λ(x, g) → a minimizer exists, and every minimizer satisfies the bound; reason: the argmin presupposes a minimizer; asserting its existence is the stronger reading
--   - encoding: argmin over X → argmin over int X; reason: g is defined on int X only
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Lemma 2.5, p.6 (citing Nemirovski and Todd 2008); Newton decrement, p.6; local norms, p.5

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_DoublyOptBandit_LocalNorm

namespace DoublyOptBandit

/-- **Lemma 2.5** (Ba, Lin, Zhang & Zhou, arXiv:2112.02856v4, Lemma 2.5, p.6; citing Nemirovski and
Todd 2008). Let `g` be a self-concordant function on `int X`, `X ⊆ ℝⁿ` closed and convex, and let
`x ∈ int X` satisfy `λ(x, g) ≤ 1/2`, where `λ(x, g) = ‖∇g(x)‖ₓ,⋆` is the Newton decrement. Then
`g` has a minimizer `x⋆` over `X`, and `‖x − x⋆‖ₓ ≤ 2λ(x, g)` in the local norm
`‖h‖ₓ = √(h⊤∇²g(x)h)` of `g`.

**Formalization Note** A self-concordant function on `int X` is encoded as the published
`ConvexOptimization.IsSelfConcordantOn (interior X) g` (convex, `C³`, `|∇³g[h,h,h]| ≤
2(∇²g[h,h])^{3/2}`) together with the closedness property `g → +∞` at `∂X`
(`EntropicBarrier.Universal.IsBarrier X g`), as in Definition 2.1 without the `ν`-inequality. The
Newton decrement and the dual norm need `∇²g(x)` nonsingular, so it is assumed positive definite.
The paper's `argmin_{x′ ∈ X} g(x′)` presupposes a minimizer; the statement asserts that one exists
(over `int X`, the domain of `g`) and bounds the distance to every minimizer. -/
theorem lemma_2_5 {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (hXcl : IsClosed X)
    (hXcv : Convex ℝ X) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hg : EntropicBarrier.Universal.IsBarrier X g ∧
      ConvexOptimization.IsSelfConcordantOn (interior X) g)
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ interior X) (hH : (hessMat g x).PosDef)
    (hlam : newtonDecrement g x ≤ 1 / 2) :
    (∃ xs ∈ interior X, IsMinOn g (interior X) xs) ∧
      ∀ xs ∈ interior X, IsMinOn g (interior X) xs →
        localNorm g x (x - xs) ≤ 2 * newtonDecrement g x := by sorry

end DoublyOptBandit
