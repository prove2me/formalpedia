-- Prove2me | Theorems.Thm_BlackScholesModel_gamma
-- name    : BlackScholesModel.gamma
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:05.166895+00:00
-- url     : https://prove2.me/theorems/35b4af86-6ee3-42ec-bfc4-cc27ba5c7a83
-- title:
--   Gamma: $\partial^2 V/\partial S^2 = N'(d_+)/(S\sigma\sqrt{T-t})$ for calls and puts
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the Delta of the call and the Delta of the put are both differentiable in the spot price at $S$, and
--
--   $$\frac{\partial^2 C}{\partial S^2}(S,t)=\frac{\partial^2 P}{\partial S^2}(S,t)=\frac{N'(d_+)}{S\sigma\sqrt{T-t}}.$$
--
--   As the source remarks, Gamma is the same for calls and puts.
--
--   **Formalization Note** The second derivative is stated as: the function $S'\mapsto\partial_S V(S',t)$ has derivative $N'(d_+)/(S\sigma\sqrt{T-t})$ at $S$.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Gamma)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem gamma (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun S' => deriv (fun S'' => callPrice K r σ T S'' t) S')
      (stdNormalPDF (dPlus S K r σ (T - t)) / (S * σ * Real.sqrt (T - t))) S ∧
    HasDerivAt (fun S' => deriv (fun S'' => putPrice K r σ T S'' t) S')
      (stdNormalPDF (dPlus S K r σ (T - t)) / (S * σ * Real.sqrt (T - t))) S := by sorry

end BlackScholesModel
