-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_prob_pos_le
-- name    : DataDrivenRO.Guarantee.prob_pos_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:42:19.376266+00:00
-- url     : https://prove2.me/theorems/00f08c51-4a1c-4d9c-a15f-f6a4ae84d0d5
-- title:
--   EC.1.1, proof of Theorem 1(a), p. ec1 — letting t ↓ 0: ℙ(f(ũ,x*) > 0) ≤ ε
-- statement:
--   Under the hypotheses of Theorem 1(a) — $0<\epsilon<1$, $\mathbb P$ a probability measure on $\mathbb R^d$, $\mathcal U$ nonempty, convex and compact with $\delta^*(\mathbf v\mid\mathcal U)\ge\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)$ for all $\mathbf v\in\mathbb R^d$ — let $f(\mathbf u,\mathbf x)$ be concave in $\mathbf u$ at $\mathbf x=\mathbf x^*$ and let $\mathbf x^*$ be robust feasible, $f(\mathbf u,\mathbf x^*)\le0$ for all $\mathbf u\in\mathcal U$. Then
--   $$\mathbb P\big(f(\tilde{\mathbf u},\mathbf x^*)>0\big)\le\epsilon .$$
--
--   It is obtained from the bound $\mathbb P(f(\tilde{\mathbf u},\mathbf x^*)\ge t)\le\epsilon$, $t>0$, by letting $t\downarrow 0$; passing to the complement gives the guarantee (2) for $f$ and $\mathbf x^*$.
--
--   **Formalization Note** Same conventions as the superlevel bound: $\delta^*$ and VaR are the published definitions, probabilities are in `ℝ≥0∞`.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.1, proof of Theorem 1(a), last sentence of the first paragraph, p. ec1

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- EC.1.1, proof of Theorem 1(a), p. ec1: letting `t ↓ 0` in `ℙ(f(ũ, x*) ≥ t) ≤ ε` gives
`ℙ(f(ũ, x*) > 0) ≤ ε`, under the hypotheses of Theorem 1(a), for every robust feasible `x*` of a
constraint concave in `u`. -/
theorem prob_pos_le {d k : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Set (Fin d → ℝ)) (hne : U.Nonempty) (hconv : Convex ℝ U) (hcpt : IsCompact U)
    (hVaR : ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v)
    (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) (xstar : Fin k → ℝ)
    (hf : ConcaveOn ℝ Set.univ (fun u => f u xstar)) (hfeas : ∀ u ∈ U, f u xstar ≤ 0) :
    P {u | 0 < f u xstar} ≤ ENNReal.ofReal ε := by sorry

end DataDrivenRO.Guarantee
