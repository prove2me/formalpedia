-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p99_options_coordinate
-- name    : CachonCoord.CapacityForecast.p99_options_coordinate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:36.020118+00:00
-- url     : https://prove2.me/theorems/fa8bba1c-22b5-4822-9d1e-72efa040da10
-- title:
--   §6.10.2, pp. 99–100 — with r − w_e = λ(r − c_p), w_o = λc_k the options contract gives Π_θ = λΩ_θ and coordinates
-- statement:
--   Consider an options contract $(w_o, w_e)$ in the capacity procurement game, with the supplier building $k = q_i$. Suppose
--   $$r - w_e = \lambda (r - c_p), \qquad w_o = \lambda c_k, \qquad \lambda \in [0, 1].$$
--   Then for every initial order $q_i$ the manufacturer's expected profit is $\Pi_\theta(q_i) = \lambda\,\Omega_\theta(q_i)$ and the supplier's is $(1 - \lambda)\,\Omega_\theta(q_i)$. Consequently any optimal capacity $k_\theta^o$ (a maximizer of $\Omega_\theta$ over $k \ge 0$) is an optimal initial order for the manufacturer and also maximizes the supplier's profit over $q_i \ge 0$: the contract coordinates the supply chain and splits its profit in the proportion $\lambda : 1 - \lambda$.
--
--   This is the coordinating contract the forced-compliance separating equilibrium of §6.10.3 is built on.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 99, the displays Π_θ(q_i) = (r − w_e)S_θ(q_i) − w_oq_i and Π_θ(q_i) = λΩ_θ(q_i), continued on p. 100

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, pp. 99–100: with `k = q_i`, an options contract whose
parameters satisfy `r − w_e = λ(r − c_p)` and `w_o = λ c_k` with `λ ∈ [0, 1]` gives the manufacturer
`Π_θ(q_i) = λ Ω_θ(q_i)` and the supplier `(1 − λ) Ω_θ(q_i)`; hence an optimal capacity `k_θ°`
(a maximizer of `Ω_θ` over `k ≥ 0`) is an optimal order for the manufacturer and also maximizes
the supplier's profit. -/
theorem p99_options_coordinate (M : Model) (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) :
    (∀ qi : ℝ, M.mfrProfit θ we wo qi = lam * M.Omega θ qi) ∧
      (∀ qi : ℝ, M.supProfit θ we wo qi = (1 - lam) * M.Omega θ qi) ∧
      IsMaxOn (fun qi => M.mfrProfit θ we wo qi) (Set.Ici 0) ko ∧
      IsMaxOn (fun qi => M.supProfit θ we wo qi) (Set.Ici 0) ko := by sorry

end CachonCoord.CapacityForecast
