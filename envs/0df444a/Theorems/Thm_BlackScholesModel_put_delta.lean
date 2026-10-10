-- Prove2me | Theorems.Thm_BlackScholesModel_put_delta
-- name    : BlackScholesModel.put_delta
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:57.457069+00:00
-- url     : https://prove2.me/theorems/1e9106b9-d588-4514-852f-d48e66b0b80c
-- title:
--   Put Delta: $\partial P/\partial S = -N(-d_+) = N(d_+) - 1$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the Black–Scholes put price is differentiable in the spot price at $S$, with
--
--   $$\frac{\partial P}{\partial S}(S,t)=-N(-d_+)=N(d_+)-1.$$
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Delta, Put)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem put_delta (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun S' => putPrice K r σ T S' t)
      (-stdNormalCDF (-dPlus S K r σ (T - t))) S ∧
    -stdNormalCDF (-dPlus S K r σ (T - t)) = stdNormalCDF (dPlus S K r σ (T - t)) - 1 := by sorry

end BlackScholesModel
