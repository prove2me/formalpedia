-- Prove2me | Theorems.Thm_ClarkeStrat_KL_theorem_11
-- name    : ClarkeStrat.KL.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:31.093987+00:00
-- url     : https://prove2.me/theorems/de06bbd7-0d14-4c36-ac8b-e0eddbf0d019
-- title:
--   Theorem 11 (Kurdyka–Łojasiewicz inequality), p. 566 — ‖∇(ψ∘f)(x)‖ ≥ 1 for 0 < f(x) ≤ χ(‖x‖) on unbounded definable submanifolds
-- statement:
--   Let $\mathcal O$ be an o-minimal structure, $U$ a nonempty definable $C^1$ submanifold of $\mathbb R^n$ (not necessarily bounded), and $f:U\to\mathbb R_+$ a definable function which is differentiable along $U$. Then there exist $\varepsilon_0>0$, a continuous definable function $\psi:[0,\varepsilon_0)\to\mathbb R_+$ with $\psi(0)=0$ which is $C^1$ on $(0,\varepsilon_0)$, and a continuous definable function $\chi:\mathbb R_+\to(0,\varepsilon_0)$ such that
--   $$\|\nabla(\psi\circ f)(x)\|\ge1\qquad\text{for all } x\in U \text{ with } 0<f(x)\le\chi(\|x\|). \tag{17}$$
--   Here $\nabla$ is the Riemannian gradient along $U$ (Remark 7). At such points $f(x)\in(0,\varepsilon_0)$, where $\psi$ is $C^1$, so $\nabla(\psi\circ f)(x)=\psi'(f(x))\nabla f(x)$ exists and the inequality is not vacuous.
--
--   The function $\chi$ makes the inequality uniform on unbounded sets: the admissible band of values shrinks as $\|x\|$ grows, but never to zero.
--
--   **Formalization Note** "Submanifold" is read as $C^1$ submanifold. $f$ is a real function on $\mathbb R^n$ of which only the values on $U$ matter; it is nonnegative and definable on $U$, and has a Riemannian gradient at each point of $U$. Inequality (17) is stated for every Riemannian gradient $g$ of $\psi\circ f$ at $x$ (it is unique).
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), p. 566, Theorem 11, (17), and Remark 7, p. 567

import Mathlib
import Definitions.Def_ClarkeStrat_KL_Setting

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared

namespace ClarkeStrat.KL

/-- Theorem 11 (Kurdyka–Łojasiewicz inequality), p. 566. Let `U` be a nonempty definable `C¹`
submanifold of `ℝⁿ` (not necessarily bounded) and `f : U → ℝ₊` a definable function, differentiable
along `U`. Then there are `ε₀ > 0`, a continuous definable `ψ : [0, ε₀) → ℝ₊`, `C¹` on `(0, ε₀)`
with `ψ(0) = 0`, and a continuous definable `χ : ℝ₊ → (0, ε₀)` such that the Riemannian gradient
of `ψ ∘ f` has norm at least `1` at every `x ∈ U` with `0 < f(x) ≤ χ(‖x‖)` (17). -/
theorem theorem_11 (O : OMinimalStructure) {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (hUne : U.Nonempty) (hUdef : U ∈ O.O n) (hUman : IsCpSubmanifold 1 U)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfdef : DefinableOn O U f) (hfnn : ∀ x ∈ U, 0 ≤ f x)
    (hfdiff : ∀ x ∈ U, ∃ g, IsRiemGrad f U x g) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ ψ χ : ℝ → ℝ,
      ContinuousOn ψ (Set.Ico 0 ε0) ∧ DefinableOn1 O (Set.Ico 0 ε0) ψ ∧
      (∀ t ∈ Set.Ico 0 ε0, 0 ≤ ψ t) ∧ ψ 0 = 0 ∧ ContDiffOn ℝ 1 ψ (Set.Ioo 0 ε0) ∧
      ContinuousOn χ (Set.Ici 0) ∧ DefinableOn1 O (Set.Ici 0) χ ∧
      (∀ s, 0 ≤ s → χ s ∈ Set.Ioo 0 ε0) ∧
      ∀ x ∈ U, 0 < f x → f x ≤ χ ‖x‖ → ∀ g, IsRiemGrad (ψ ∘ f) U x g → 1 ≤ ‖g‖ := by sorry

end ClarkeStrat.KL
