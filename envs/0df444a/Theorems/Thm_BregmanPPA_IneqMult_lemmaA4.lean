-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_lemmaA4
-- name    : BregmanPPA.IneqMult.lemmaA4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:47.014984+00:00
-- url     : https://prove2.me/theorems/f83601a8-b759-4a44-9264-8dae006e6b17
-- title:
--   Lemma A4 — a subdifferential chain rule for nondecreasing convex composition
-- statement:
--   Let $F_i$ be proper convex functions on $\mathbb R^n$ whose effective domains have a common relative-interior point. Let $F_0$ be a proper convex function on $\mathbb R^m$ that is nondecreasing in every coordinate, and let $G(x)=F_0(F_1(x),\ldots,F_m(x))$ when every inner value is finite, with $G(x)=+\infty$ otherwise. Then $G$ is convex. At any point $x_0$ where every inner value is finite and $F_0$ is finite near the vector of inner values and differentiable there, $G$ is proper and
--
--   $$\partial G(x_0)=\sum_{i=1}^m[\nabla F_0(F(x_0))]_i\,\partial F_i(x_0)+N_{\operatorname{dom}G}(x_0).$$
--
--   The chain rule is used for the first-order condition of the primal subproblem in the proof of Theorem 7.
--
--   **Formalization Note** The paper prints “Lemma 5” when referring to monotonicity; Lemma 2 is intended. It also prints the first case of $G$ as “$f(x)\in\mathbb R^n$”; $\mathbb R^m$ is intended. Convexity of $G$ is stated unconditionally, as on the page. The paper's unconditional claim that $G$ is proper is false without a point of $\operatorname{dom}G$ (take $m=1$, $F_1\equiv0$ and $F_0$ the indicator of $(-\infty,-1]$, so $G\equiv+\infty$); properness is therefore stated at the point $x_0$ of the chain rule, which supplies that witness. Local finiteness makes differentiability of the extended-real outer function meaningful. A zero coefficient contributes zero even if the corresponding inner subdifferential is empty.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 224, Lemma A4, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.IneqMult

/-- Lemma A4, p. 224: the subdifferential chain rule. `G` is convex unconditionally;
properness needs a point of `dom G`, supplied by any `x₀` at which every inner value is
finite and `F₀` is finite near (hence differentiable at) the vector of inner values. -/
theorem lemmaA4 {n m : ℕ} (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hri : ∃ x : E n, ∀ i,
      x ∈ intrinsicInterior ℝ {y : E n | F i y ≠ ⊤})
    (hF₀ : IsProperFn F₀ ∧ IsConvexFn F₀)
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v) :
    IsConvexFn (compositeFn F F₀) ∧
    ∀ x₀ : E n, (∀ i, F i x₀ ≠ ⊤) →
      (∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤) →
      DifferentiableAt ℝ (fun z : E m => (F₀ z).toReal) (gvec F x₀) →
      IsProperFn (compositeFn F F₀) ∧
      BregmanPPA.Convergence.subdiffOp (compositeFn F F₀) x₀ =
        {v | ∃ ν : E n,
          ν ∈ normalCone {x | compositeFn F F₀ x ≠ ⊤} x₀ ∧
          ∃ ξ : Fin m → E n,
            (∀ i, (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) i ≠ 0 →
              IsSubgradient (F i) x₀ (ξ i)) ∧
            v = ν + ∑ i, (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) i • ξ i} := by sorry

end BregmanPPA.IneqMult
