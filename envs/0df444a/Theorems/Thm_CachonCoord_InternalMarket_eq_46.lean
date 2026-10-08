-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_eq_46
-- name    : CachonCoord.InternalMarket.eq_46
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:07.256013+00:00
-- url     : https://prove2.me/theorems/977ee0df-0d02-4f28-a9d5-8c646b044819
-- title:
--   Eq. (46), p. 94 — the payment ((η−1)/η)(e°)^{−1/η} E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]/E[Y] equals E[Qw(A, Q)|e°]/E[Q|e°]
-- statement:
--   In the model of §6.9.1, assume the integrand of $K=E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]$ is integrable and $E[Y]>0$. Then for every effort $e^o>0$, with realized output $Q=Ye^o$,
--   $$
--   \Big(\frac{\eta-1}{\eta}\Big)(e^o)^{-1/\eta}\,E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]\big/E[Y]=\frac{E[Q\,w(A,Q)\mid e^o]}{E[Q\mid e^o]}. \qquad (46)
--   $$
--
--   The left side is the per-unit payment to the production manager; the identity says it is the expected shadow price of capacity, weighted by output.
--
--   **Formalization Note** $E[Y]>0$ is added: $Y\in[0,1]$ alone allows $Y=0$ almost surely, where both sides of (46) divide by zero. At a realization with $Y=0$ the output is $Q=0$ and $Q\,w(A,Q)$ is taken to be $0$ (its limit).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, Eq. (46), p. 94

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- Eq. (46), §6.9.1, p. 94 (Cachon 2003, 3rd draft): if `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` is
integrable and `E[Y] > 0`, then for every effort `e° > 0` the per-unit payment
`((η − 1)/η)(e°)^{−1/η} K / E[Y]` equals `E[Q w(A, Q) | e°] / E[Q | e°]` with `Q = Y e°`. -/
theorem eq_46 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P)
    (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.payRate eo = M.expMarketRevenue eo / M.expOutput eo := by sorry

end CachonCoord.InternalMarket
