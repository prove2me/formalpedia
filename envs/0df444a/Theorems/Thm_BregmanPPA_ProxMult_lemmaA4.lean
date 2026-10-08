-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_lemmaA4
-- name    : BregmanPPA.ProxMult.lemmaA4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:48.551989+00:00
-- url     : https://prove2.me/theorems/1e8cfb39-7a13-4d22-ae77-38b5a809c2ec
-- title:
--   Lemma A4 — a subdifferential chain rule for f₀ ∘ (f₁, …, f_m) with f₀ nondecreasing
-- statement:
--   Let $f_1,\dots,f_m$ be proper convex functions on $\mathbb R^n$ with $\bigcap_{i=1}^m\operatorname{ri}(\operatorname{dom}f_i)\ne\emptyset$, and write $f(x)=(f_1(x),\dots,f_m(x))\in(-\infty,+\infty]^m$. Let $f_0$ be a proper convex function on $\mathbb R^m$ which is nondecreasing ($u\le v$ componentwise implies $f_0(u)\le f_0(v)$). Define $G:\mathbb R^n\to(-\infty,+\infty]$ by $G(x)=f_0(f(x))$ when $f(x)\in\mathbb R^m$ and $G(x)=+\infty$ when $f_i(x)=+\infty$ for some $i$. Then $G$ is proper and convex, and if $f_0$ is differentiable at $f(x^0)\in\mathbb R^m$, with $y=\nabla f_0(f(x^0))$,
--
--   $$\partial G(x^0)=\sum_{i=1}^m y_i\,\partial f_i(x^0)+N_{\operatorname{dom}G}(x^0).$$
--
--   The lemma computes $\partial G_k$ for $G_k(x)=\frac1{c_k}h_p^{*+}(\nabla h_p(p^k)+c_kg(x))$ in the proof of (14).
--
--   **Formalization Note** The paper says "nondecreasing in the sense of Lemma 5" and, in the definition of $G$, "$f(x)\in\mathbb R^n$"; the paper has no Lemma 5 and $f(x)$ has $m$ components, so the intended readings are Lemma 2 and $\mathbb R^m$. "$f_0$ differentiable at $f(x^0)\in\mathbb R^m$" is encoded as: each $f_i(x^0)$ finite, $f_0$ finite on a neighbourhood of $f(x^0)$, and the real function $z\mapsto f_0(z)$ differentiable there. The sum is a Minkowski sum, and a term with $y_i=0$ is $\{0\}$, following the proof's convention (p. 225, where the terms with $y_i=0$ are absorbed into the normal cones of $\operatorname{dom}f_i$): $v\in$ RHS iff $v=\nu+\sum_i y_i\xi_i$ with $\nu\in N_{\operatorname{dom}G}(x^0)$ and $\xi_i\in\partial f_i(x^0)$ whenever $y_i\ne0$. $\operatorname{ri}$ is Mathlib's `intrinsicInterior`.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 224, Lemma A4

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.ProxMult

/-- Lemma A4 (a subdifferential chain rule), p. 224. `F i` are the paper's `fᵢ`, `F₀` is `f₀`
(nondecreasing in the sense of Lemma 2), `compositeFn F F₀` is `G`. "`f₀` differentiable at
`f(x⁰) ∈ ℝᵐ`" is: every `fᵢ(x⁰)` finite, `f₀` finite near `f(x⁰)`, and its real version
differentiable there. In the sum, a term with coefficient `0` is `{0}` (the paper's convention,
p. 225). -/
theorem lemmaA4 {n m : ℕ} (F : Fin m → BregmanPPA.IneqMult.E n → EReal) (F₀ : BregmanPPA.IneqMult.E m → EReal) (x₀ : BregmanPPA.IneqMult.E n)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hri : ∃ x : BregmanPPA.IneqMult.E n, ∀ i, x ∈ intrinsicInterior ℝ {y : BregmanPPA.IneqMult.E n | F i y ≠ ⊤})
    (hF₀ : IsProperFn F₀ ∧ IsConvexFn F₀)
    (hmono : ∀ u v : BregmanPPA.IneqMult.E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v)
    (hfinite : ∀ i, F i x₀ ≠ ⊤)
    (hF₀near : ∀ᶠ z in 𝓝 (BregmanPPA.IneqMult.gvec F x₀), F₀ z ≠ ⊤)
    (hdiff : DifferentiableAt ℝ (fun z : BregmanPPA.IneqMult.E m => (F₀ z).toReal) (BregmanPPA.IneqMult.gvec F x₀)) :
    IsProperFn (BregmanPPA.IneqMult.compositeFn F F₀) ∧
    IsConvexFn (BregmanPPA.IneqMult.compositeFn F F₀) ∧
    BregmanPPA.Convergence.subdiffOp (BregmanPPA.IneqMult.compositeFn F F₀) x₀ =
      {v | ∃ ν : BregmanPPA.IneqMult.E n, ν ∈ BregmanPPA.IneqMult.normalCone {x | BregmanPPA.IneqMult.compositeFn F F₀ x ≠ ⊤} x₀ ∧
        ∃ ξ : Fin m → BregmanPPA.IneqMult.E n,
          (∀ i, (gradient (fun z : BregmanPPA.IneqMult.E m => (F₀ z).toReal) (BregmanPPA.IneqMult.gvec F x₀)) i ≠ 0 →
            IsSubgradient (F i) x₀ (ξ i)) ∧
          v = ν + ∑ i, (gradient (fun z : BregmanPPA.IneqMult.E m => (F₀ z).toReal) (BregmanPPA.IneqMult.gvec F x₀)) i • ξ i} := by sorry

end BregmanPPA.ProxMult
