-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_prob_superlevel_le
-- name    : DataDrivenRO.Guarantee.prob_superlevel_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:41:59.30545+00:00
-- url     : https://prove2.me/theorems/957f68a1-6ebe-4662-939c-94b41d51c734
-- title:
--   EC.1.1, proof of Theorem 1(a), p. ec1 — ℙ(f(ũ,x*) ≥ t) ≤ ε for every t > 0
-- statement:
--   Let $0<\epsilon<1$, let $\mathbb P$ be a probability measure on $\mathbb R^d$, and let $\mathcal U\subseteq\mathbb R^d$ be nonempty, convex and compact with
--   $$\delta^*(\mathbf v\mid\mathcal U)\ge\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)\qquad\forall\,\mathbf v\in\mathbb R^d .$$
--   Let $f(\mathbf u,\mathbf x)$, $\mathbf x\in\mathbb R^k$, be concave in $\mathbf u$ at $\mathbf x=\mathbf x^*$, and let $\mathbf x^*$ be robust feasible: $f(\mathbf u,\mathbf x^*)\le 0$ for all $\mathbf u\in\mathcal U$. Then for every $t>0$,
--   $$\mathbb P\big(f(\tilde{\mathbf u},\mathbf x^*)\ge t\big)\le\epsilon .$$
--
--   This is the chain $\mathbb P(f(\tilde{\mathbf u},\mathbf x^*)\ge t)\le\mathbb P(\mathbf v^T\tilde{\mathbf u}>v_0)\le\mathbb P(\mathbf v^T\tilde{\mathbf u}>\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v))\le\epsilon$ of the proof of Theorem 1(a), whose endpoints are stated here.
--
--   **Formalization Note** $\delta^*$ is the published `RobustMDP.Shared.supportFunction` and VaR the published `MultistageStochastic.valueAtRisk` at level $1-\epsilon$; the compactness and nonemptiness of $\mathcal U$ make $\delta^*$ a genuine maximum. Probabilities are in `ℝ≥0∞`, compared with `ENNReal.ofReal ε`.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.1, proof of Theorem 1(a), second display, p. ec1

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- EC.1.1, proof of Theorem 1(a), p. ec1: under the hypotheses of Theorem 1(a)
(`U` nonempty, convex, compact and `δ*(v|U) ≥ VaR^ℙ_ε(v)` for all `v`), for a robust feasible `x*`
of a constraint concave in `u` and every `t > 0`, `ℙ(f(ũ, x*) ≥ t) ≤ ε`. -/
theorem prob_superlevel_le {d k : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Set (Fin d → ℝ)) (hne : U.Nonempty) (hconv : Convex ℝ U) (hcpt : IsCompact U)
    (hVaR : ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v)
    (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) (xstar : Fin k → ℝ)
    (hf : ConcaveOn ℝ Set.univ (fun u => f u xstar)) (hfeas : ∀ u ∈ U, f u xstar ≤ 0)
    (t : ℝ) (ht : 0 < t) :
    P {u | t ≤ f u xstar} ≤ ENNReal.ofReal ε := by sorry

end DataDrivenRO.Guarantee
