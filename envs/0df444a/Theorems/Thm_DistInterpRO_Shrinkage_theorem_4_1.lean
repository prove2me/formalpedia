-- Prove2me | Theorems.Thm_DistInterpRO_Shrinkage_theorem_4_1
-- name    : DistInterpRO.Shrinkage.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:54:26.80017+00:00
-- url     : https://prove2.me/theorems/d3e585b7-4133-4b1f-9769-476b386037ce
-- title:
--   Theorem 4.1 — Shrinking Δ to αΔ solves the two-scenario DRSP problem within αD²h
-- statement:
--   Let $V$ be a set of decisions and $f:V\times\mathbb{R}^m\to\mathbb{R}$. Fix a nominal parameter $x_0\in\mathbb{R}^m$, a compact deviation set $\Delta\subseteq\mathbb{R}^m$ with $0\in\Delta$, and $\alpha\in(0,1)$. Suppose that for every $v$, $f(v,\cdot)$ is twice differentiable with a uniformly bounded Hessian: there exists $h\ge0$ such that for all $v,x$
--   $$-hI\preceq H_v(x)\preceq hI,$$
--   where $H_v(x)$ is the Hessian of $f(v,\cdot)$ at $x$ and $\preceq$ is the positive-semidefinite order. Let $D=\max_{x\in\Delta}\|x\|_2$ and $\hat{\mathcal P}'=\{\mu\in\mathcal P\mid\mu(\{x_0\})\ge1-\alpha,\ \mu(x_0+\Delta)=1\}$. Then for all $v$ the minimum of $f(v,x_0+\cdot)$ over $\alpha\Delta$ is attained and
--   $$\inf_{\mu\in\hat{\mathcal P}'}\int_{\mathbb{R}^m}f(v,x)\,d\mu(x)-\alpha D^2h\le\min_{x_\delta\in\alpha\Delta}f(v,x_0+x_\delta)\le\inf_{\mu\in\hat{\mathcal P}'}\int_{\mathbb{R}^m}f(v,x)\,d\mu(x)+\alpha D^2h.$$
--
--   The theorem justifies the practice of shrinking an uncertainty set: the $\alpha$-shrunken robust problem approximately solves a two-scenario distributionally robust problem in which the parameter takes its nominal value with probability at least $1-\alpha$ and otherwise deviates within $\Delta$.
--
--   **Formalization Note** Two hypotheses are implicit on the page and are made explicit: $\Delta$ is compact (so the paper's min and max are attained and $D$ is finite) and $0\in\Delta$ (without it $\hat{\mathcal P}'$ is empty; the page's two-scenario reading presupposes the nominal point is a possible parameter). The Hessian bound is the quadratic-form bound $|D^2f(v,\cdot)(x)[y,y]|\le h\|y\|_2^2$ with $f(v,\cdot)$ and its derivative differentiable everywhere; $h$ is one constant for all $v$. The min over $\alpha\Delta$ is written as a real infimum over the subtype, together with a separate attainment clause; the infimum over $\hat{\mathcal P}'$ is the real infimum `drspValue` of Bochner integrals, which are finite because $f(v,\cdot)$ is continuous and every $\mu\in\hat{\mathcal P}'$ is carried by the compact set $x_0+\Delta$.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 104, Theorem 4.1

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- Theorem 4.1 (Xu–Caramanis–Mannor 2012, p. 104). If there is `h ≥ 0` with
`−hI ⪯ H_v(x) ⪯ hI` for all `v, x`, then for all `v` the minimum over `αΔ` is attained and
`inf_{μ∈𝒫̂′} ∫ f(v, x) dμ(x) − αD²h ≤ min_{x_δ∈αΔ} f(v, x₀ + x_δ)
  ≤ inf_{μ∈𝒫̂′} ∫ f(v, x) dμ(x) + αD²h`,
with `D = max_{x∈Δ} ‖x‖₂` and `𝒫̂′ = {μ ∈ 𝒫 | μ({x₀}) ≥ 1 − α, μ(x₀ + Δ) = 1}`.
Added standing hypotheses (implicit on the page): `Δ` compact and `0 ∈ Δ`. -/
theorem theorem_4_1 {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : ∀ v, HasBoundedHessian (f v) h) :
    ∀ v : V,
      (∃ x ∈ α • Δ, ∀ y ∈ α • Δ, f v (x₀ + x) ≤ f v (x₀ + y)) ∧
      drspValue (f v) x₀ Δ (1 - α) - α * devRadius Δ ^ 2 * h ≤
        (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ∧
      (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ≤
        drspValue (f v) x₀ Δ (1 - α) + α * devRadius Δ ^ 2 * h := by sorry

end DistInterpRO.Shrinkage
