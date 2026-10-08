-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p100_voluntary_compliance
-- name    : CachonCoord.CapacityForecast.p100_voluntary_compliance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:42.292824+00:00
-- url     : https://prove2.me/theorems/3a2cb238-0b8b-4e2e-b54f-cdadb30e30fe
-- title:
--   §6.10.2, p. 100 — under voluntary compliance ∂π(k_θ°, k_θ°, θ)/∂k < 0, so k_θ° is not the supplier's optimum
-- statement:
--   Take the coordinating options contract of p. 99, $r - w_e = \lambda(r - c_p)$ and $w_o = \lambda c_k$, with $0 < \lambda \le 1$, and suppose the supplier may build less capacity than the options sold (voluntary compliance). A supplier who believes demand is type $\tau$, has sold $q_i$ options and builds $k$ units earns
--   $$\pi(k, q_i, \tau) = (w_e - c_p)S_\tau(k) + w_o q_i - c_k k = (1 - \lambda)(r - c_p)S_\tau(k) - c_k(k - \lambda q_i).$$
--   Let $k_\theta^o > 0$ be an optimal capacity of type $\theta$. Then
--   $$\frac{\partial \pi(k_\theta^o, k_\theta^o, \theta)}{\partial k} < 0,$$
--   so $k_\theta^o$ does not maximize the supplier's profit over $0 \le k \le q_i$ when $q_i = k_\theta^o$.
--
--   This is why coordination with the options contract requires forced compliance.
--
--   **Formalization Note** The page allows $\lambda \in [0,1]$; at $\lambda = 0$ the derivative is $0$, so the strict claim needs $\lambda > 0$, which is assumed. The partial derivative is taken in $k$ with $q_i = k_\theta^o$ fixed. The page writes $s_\tau(k)$ for $S_\tau(k)$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 100, the displays π(k, q_i, τ) and ∂π(k_θ°, k_θ°, θ)/∂k < 0

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 100: under the coordinating options contract
(`r − w_e = λ(r − c_p)`, `w_o = λ c_k`, here with `λ ∈ (0, 1]`), the profit of a supplier who
believes demand is type `θ` and builds `k` after selling `q_i` options is
`π(k, q_i, θ) = (1 − λ)(r − c_p) S_θ(k) − c_k (k − λ q_i)`; at `q_i = k = k_θ°` its derivative in `k`
is negative, so `k_θ°` does not maximize the supplier's profit over `0 ≤ k ≤ q_i`. -/
theorem p100_voluntary_compliance (M : Model) (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) (hko_pos : 0 < ko) :
    (∀ k qi : ℝ, M.supVoluntaryProfit θ we wo k qi
        = (1 - lam) * (M.r - M.cp) * M.S θ k - M.ck * (k - lam * qi)) ∧
      (∃ d : ℝ, d < 0 ∧ HasDerivAt (fun k => M.supVoluntaryProfit θ we wo k ko) d ko) ∧
      ¬ IsMaxOn (fun k => M.supVoluntaryProfit θ we wo k ko) (Set.Icc 0 ko) ko := by sorry

end CachonCoord.CapacityForecast
