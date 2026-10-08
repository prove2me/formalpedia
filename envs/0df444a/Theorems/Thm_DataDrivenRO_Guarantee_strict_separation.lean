-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_strict_separation
-- name    : DataDrivenRO.Guarantee.strict_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:41:49.490286+00:00
-- url     : https://prove2.me/theorems/6445d29d-65e5-46ff-b547-62777a1657ad
-- title:
--   EC.1.1, proof of Theorem 1(a), p. ec1 — a strict separating hyperplane between 𝒰 and {u : f(u,x*) ≥ t}
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^d$ be nonempty, convex and compact, let $f(\mathbf u,\mathbf x)$ be a function with $\mathbf x\in\mathbb R^k$, and let $\mathbf x^*\in\mathbb R^k$ be such that $\mathbf u\mapsto f(\mathbf u,\mathbf x^*)$ is concave on $\mathbb R^d$ and $\mathbf x^*$ is robust feasible: $f(\mathbf u,\mathbf x^*)\le 0$ for all $\mathbf u\in\mathcal U$. Then for every $t>0$ there exist $\mathbf v\in\mathbb R^d$ and $v_0\in\mathbb R$ such that
--   $$\mathbf v^T\mathbf u<v_0\quad\forall\,\mathbf u\in\mathcal U,\qquad\qquad \mathbf v^T\mathbf u>v_0\quad\forall\,\mathbf u\in\{\mathbf u\in\mathbb R^d: f(\mathbf u,\mathbf x^*)\ge t\}.$$
--
--   This is the separation step of the proof of Theorem 1(a): the hyperplane $\mathbf v^T\mathbf u=v_0$ strictly separates the uncertainty set from the closed convex superlevel set of the constraint, which is disjoint from $\mathcal U$.
--
--   **Formalization Note** The page prints "$\mathbf v^T\mathbf u<v_0$" on the superlevel set as well, a slip: a separating hyperplane puts the two sets on opposite sides, and the next display of the proof uses $\mathbb P(f(\tilde{\mathbf u},\mathbf x^*)\ge t)\le\mathbb P(\mathbf v^T\tilde{\mathbf u}>v_0)$. The statement uses the corrected side. When the superlevel set is empty the second clause holds vacuously.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.1, proof of Theorem 1(a), second sentence, p. ec1

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- EC.1.1, proof of Theorem 1(a), p. ec1: if `U` is nonempty, convex and compact, `f(·, x*)` is
concave on `ℝᵈ`, `x*` is robust feasible and `t > 0`, there is a hyperplane `vᵀu = v₀` strictly
separating `U` (where `vᵀu < v₀`) from the superlevel set `{u : f(u, x*) ≥ t}` (where `vᵀu > v₀`). -/
theorem strict_separation {d k : ℕ} (U : Set (Fin d → ℝ)) (hne : U.Nonempty) (hconv : Convex ℝ U)
    (hcpt : IsCompact U) (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) (xstar : Fin k → ℝ)
    (hf : ConcaveOn ℝ Set.univ (fun u => f u xstar)) (hfeas : ∀ u ∈ U, f u xstar ≤ 0)
    (t : ℝ) (ht : 0 < t) :
    ∃ (v : Fin d → ℝ) (v₀ : ℝ), (∀ u ∈ U, u ⬝ᵥ v < v₀) ∧ (∀ u, t ≤ f u xstar → v₀ < u ⬝ᵥ v) := by sorry

end DataDrivenRO.Guarantee
