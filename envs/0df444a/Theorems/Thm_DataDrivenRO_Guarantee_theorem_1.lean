-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_theorem_1
-- name    : DataDrivenRO.Guarantee.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:42:35.432371+00:00
-- url     : https://prove2.me/theorems/5d393605-9705-4cbc-a190-9bde5abdd70a
-- title:
--   Theorem 1, p. 10 — δ*(v|𝒰) ≥ VaR^ℙ_ε(v) ∀v implies the probabilistic guarantee for every concave f; failure at one v breaks it for a bi-affine f
-- statement:
--   Let $0<\epsilon<1$ and let $\mathbb P$ be a probability measure on $\mathbb R^d$. Write $\delta^*(\mathbf v\mid\mathcal U)=\sup_{\mathbf u\in\mathcal U}\mathbf v^T\mathbf u$ and $\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)=\inf\{t:\mathbb P(\tilde{\mathbf u}^T\mathbf v\le t)\ge1-\epsilon\}$.
--
--   1. **(a)** If $\mathcal U\subseteq\mathbb R^d$ is nonempty, convex and compact and
--   $$\delta^*(\mathbf v\mid\mathcal U)\ge\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)\qquad\forall\,\mathbf v\in\mathbb R^d,$$
--   then $\mathcal U$ implies a probabilistic guarantee at level $\epsilon$ for $\mathbb P$: for every $k$, every $f(\mathbf u,\mathbf x)$ concave in $\mathbf u$ for every $\mathbf x\in\mathbb R^k$, and every $\mathbf x^*\in\mathbb R^k$ with $f(\mathbf u,\mathbf x^*)\le0$ for all $\mathbf u\in\mathcal U$, one has $\mathbb P(f(\tilde{\mathbf u},\mathbf x^*)\le0)\ge1-\epsilon$.
--   2. **(b)** If $\mathcal U$ is nonempty and $\delta^*(\mathbf v\mid\mathcal U)<\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)$ for some $\mathbf v\in\mathbb R^d$ at which $\delta^*(\mathbf v\mid\mathcal U)$ is finite, then there is a bi-affine function $f(\mathbf u,x)$, $x\in\mathbb R$, for which (2) fails: some $x^*$ satisfies $f(\mathbf u,x^*)\le0$ for all $\mathbf u\in\mathcal U$, yet $\mathbb P(f(\tilde{\mathbf u},x^*)\le0)<1-\epsilon$.
--
--   Theorem 1 reduces the design of uncertainty sets with a probabilistic guarantee to a comparison of two functions of $\mathbf v$: the support function of the set and the Value at Risk of the linear loss in direction $\mathbf v$. Every construction of the paper (Sections 4–8) is certified through part (a). Part (b) is not the converse of (a): it says that failing the condition at one direction already breaks the guarantee for some bi-affine constraint.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`; $\delta^*$ and VaR are the published `RobustMDP.Shared.supportFunction` and `MultistageStochastic.valueAtRisk` (at level $1-\epsilon$). The paper fixes $0<\epsilon<1$ in its schema (p. 10); for $\epsilon\ge1$ the infimum (6) is $-\infty$. Part (b) is printed with $\mathcal U^*$, a slip for $\mathcal U$. In part (b), "$\delta^*(\mathbf v\mid\mathcal U)<\mathrm{VaR}$" between extended reals means $\delta^*(\mathbf v\mid\mathcal U)$ is finite; this is stated as $\mathcal U$ nonempty and $\{\mathbf v^T\mathbf u:\mathbf u\in\mathcal U\}$ bounded above, since the published support function is $0$ on empty or unbounded-above images, which would otherwise let the hypothesis hold for the wrong reason. $\mathcal U$ itself may be unbounded. (For $\mathcal U=\emptyset$ the paper's (b) is trivial, a constant $f>0$ breaking (2); it is excluded.) Part (b)'s bi-affine witness uses a scalar decision variable (`Fin 1 → ℝ`), as the proof does.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 1, p. 10 (proof EC.1.1, p. ec1)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- Theorem 1, p. 10 (proof EC.1.1, p. ec1), for `0 < ε < 1` and a probability measure `ℙ`
on `ℝᵈ`.
(a) If `U` is nonempty, convex and compact and `δ*(v|U) ≥ VaR^ℙ_ε(v)` for every `v ∈ ℝᵈ`, then
`U` implies a probabilistic guarantee at level `ε` for `ℙ` (for every `f(u, x)` concave in `u`).
(b) If `U` is nonempty and `δ*(v|U) < VaR^ℙ_ε(v)` for some `v` at which `δ*(v|U)` is finite
(`{vᵀu : u ∈ U}` bounded above), then some bi-affine
`f(u, x)` (with `x ∈ ℝ¹`) violates (2): some `x*` is robust feasible but
`ℙ(f(ũ, x*) ≤ 0) < 1 − ε`. -/
theorem theorem_1 {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ U : Set (Fin d → ℝ), U.Nonempty → Convex ℝ U → IsCompact U →
      (∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v) → ImpliesGuarantee P U ε) ∧
    (∀ U : Set (Fin d → ℝ), U.Nonempty →
      (∃ v, BddAbove ((fun u => u ⬝ᵥ v) '' U) ∧
        RobustMDP.Shared.supportFunction U v < VaR P ε v) →
      ∃ f : (Fin d → ℝ) → (Fin 1 → ℝ) → ℝ, IsBiaffine f ∧ ∃ xstar : Fin 1 → ℝ,
        (∀ u ∈ U, f u xstar ≤ 0) ∧ P {u | f u xstar ≤ 0} < ENNReal.ofReal (1 - ε)) := by sorry

end DataDrivenRO.Guarantee
