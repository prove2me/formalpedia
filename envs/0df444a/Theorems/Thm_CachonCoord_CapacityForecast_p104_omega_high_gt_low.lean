-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p104_omega_high_gt_low
-- name    : CachonCoord.CapacityForecast.p104_omega_high_gt_low
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:46.282728+00:00
-- url     : https://prove2.me/theorems/6646d90d-20e4-482c-ad13-22d397ddf4cf
-- title:
--   §6.10.3, p. 104 (implicit) — Ω_l(k) < Ω_h(k) for k > 0, hence Ω_l° < Ω_h°
-- statement:
--   In the capacity procurement game, high demand stochastically dominates low demand, $F(x\mid h) < F(x\mid l)$ for $x \ge 0$. Then the supply chain earns more under high demand at every positive capacity,
--   $$\Omega_l(k) < \Omega_h(k) \quad (k > 0),$$
--   and consequently, if $k_h^o$ and $k_l^o$ maximize $\Omega_h$ and $\Omega_l$ over $k \ge 0$ and $k_l^o > 0$,
--   $$\Omega_l^o = \Omega_l(k_l^o) < \Omega_h(k_h^o) = \Omega_h^o .$$
--
--   This comparison is the step behind the page's "Since $\min\{\lambda_h, \hat\lambda_h\} > \lambda_l$" and "a lower profit ($\Omega_h(k_l^o)$ vs. $\Omega_h^o$)" on p. 104.
--
--   **Formalization Note** The page does not state this as a separate sentence; it is used implicitly in the argument on p. 104 and is cited as such.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.3, p. 104, implicit in 'Since min{λ_h, λ̂_h} > λ_l'

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.3, p. 104, implicit in "Since min{λ_h, λ̂_h} > λ_l" and in
"a lower profit (Ω_h(k_l°) vs. Ω_h°)": because `D_h` stochastically dominates `D_l`, the chain
earns more with high demand at every positive capacity, `Ω_l(k) < Ω_h(k)` for `k > 0`, and hence
the optimal high-type profit exceeds the optimal low-type profit, `Ω_l° < Ω_h°`, where `kh`, `kl`
are optimal capacities (maximizers of `Ω_h`, `Ω_l` over `k ≥ 0`) and `k_l° > 0`. -/
theorem p104_omega_high_gt_low (M : Model) (kh kl : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl) :
    (∀ k : ℝ, 0 < k → M.Omega DemandType.l k < M.Omega DemandType.h k) ∧
      M.Omega DemandType.l kl < M.Omega DemandType.h kh := by sorry

end CachonCoord.CapacityForecast
