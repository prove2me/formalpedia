-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p104_forced_compliance_separating
-- name    : CachonCoord.CapacityForecast.p104_forced_compliance_separating
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:47.107267+00:00
-- url     : https://prove2.me/theorems/9f066c31-6751-48e9-ba2d-157cf1bdb8b7
-- title:
--   §6.10.3, pp. 103–104 — under forced compliance the options contracts with shares λ_l and min{λ_h, λ̂_h} separate the types and coordinate
-- statement:
--   Consider the capacity procurement game with forced compliance (the supplier must build $k = q_i$). Let $k_h^o, k_l^o > 0$ be optimal capacities (maximizers of $\Omega_h$, $\Omega_l$ over $k \ge 0$), $\Omega_\theta^o = \Omega_\theta(k_\theta^o)$, and let $\hat\pi$ be the supplier's minimum acceptable profit, with $0 < \hat\pi < \Omega_l^o$ and $\Omega_l(k_h^o) > 0$. Define
--   $$\lambda_l = 1 - \frac{\hat\pi}{\Omega_l^o}, \qquad \lambda_h = 1 - \frac{\hat\pi}{\Omega_h^o}, \qquad \hat\lambda_h = \frac{\Omega_l^o - \hat\pi}{\Omega_l(k_h^o)}, \qquad \lambda_H = \min\{\lambda_h, \hat\lambda_h\}.$$
--   The low type offers the coordinating options contract of p. 99 with share $\lambda_l$ and initial order $k_l^o$; the high type offers the one with share $\lambda_H$ and initial order $k_h^o$. Then:
--
--   1. $\lambda_l, \lambda_H \in (0, 1)$, and $\lambda_l < \lambda_h$, $\lambda_l < \hat\lambda_h$, so $\lambda_l < \lambda_H$;
--   2. the high type strictly prefers her contract to the low type's: $\lambda_l\,\Omega_h(k_l^o) < \lambda_H\,\Omega_h^o$ (her profits under the two contracts);
--   3. the low type weakly prefers her contract to the high type's: $\lambda_H\,\Omega_l(k_h^o) \le \lambda_l\,\Omega_l^o = \Omega_l^o - \hat\pi$;
--   4. the supplier accepts both: he earns exactly $\hat\pi$ from the low type and at least $\hat\pi$ from the high type, exactly $\hat\pi$ when $\lambda_h \le \hat\lambda_h$;
--   5. each contract coordinates: the initial order $k_\theta^o$ maximizes both the type-$\theta$ manufacturer's and the supplier's expected profit over $q_i \ge 0$.
--
--   These are the incentive-compatibility, participation and coordination conditions that make the two contracts a separating equilibrium in which the high-demand forecast is shared credibly and the supply chain is coordinated in every state.
--
--   **Formalization Note** The page's "separating equilibrium" is formalized by its defining conditions (p. 103: each type prefers her own contract, the supplier accepts) stated as inequalities between the firms' profits, not by a general signalling-game equilibrium concept. Each profit is the contract's profit function evaluated at the offered contract, so clauses 2–4 are inequalities between $\Pi_\theta$ and supplier profits, not between shares. Added hypotheses, all disclosed: $\hat\pi > 0$ (needed for $\lambda_l < \lambda_h$ strictly) and $\hat\pi < \Omega_l^o$ (needed for $\lambda_l > 0$); $\Omega_l(k_h^o) > 0$ (the page divides by it); $k_\theta^o > 0$ is footnote 46's assumption. The prior $\rho$ plays no role and does not appear.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.3, p. 103 (forced compliance, π̂) and p. 104, the separating options contracts λ_l, λ_h, λ̂_h and the paragraph following them

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.3, pp. 103–104, the forced-compliance separating contracts.
`kh`, `kl` are optimal capacities `k_h°, k_l° > 0` (maximizers of `Ω_h`, `Ω_l` over `k ≥ 0`),
`piHat` is the supplier's minimum acceptable profit `π̂` with `0 < π̂ < Ω_l°`, and `Ω_l(k_h°) > 0`.
The low type offers the coordinating options contract with share `λ_l = 1 − π̂/Ω_l°` and initial
order `k_l°`; the high type offers share `λ_H = min{λ_h, λ̂_h}`, `λ_h = 1 − π̂/Ω_h°`,
`λ̂_h = (Ω_l° − π̂)/Ω_l(k_h°)`, and initial order `k_h°`; under forced compliance `k = q_i`. Then:
both shares lie in `(0, 1)` and `λ_l < λ_h`, `λ_l < λ̂_h`; the high type strictly prefers her contract
to the low type's; the low type weakly prefers hers to the high type's; the supplier earns exactly
`π̂` from the low type, at least `π̂` from the high type, and exactly `π̂` when `λ_h ≤ λ̂_h`; and each
type's initial order maximizes both her own and the supplier's profit (coordination). -/
theorem p104_forced_compliance_separating (M : Model) (kh kl piHat : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh) (hkh_pos : 0 < kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl)
    (hpi_pos : 0 < piHat) (hpi_lt : piHat < M.Omega DemandType.l kl)
    (hcross : 0 < M.Omega DemandType.l kh) :
    let lamL := M.shareLow kl piHat
    let lamH := min (M.shareHigh kh piHat) (M.shareHighHat kh kl piHat)
    -- the shares are admissible and the high type's share is larger
    (0 < lamL ∧ lamL < 1 ∧ 0 < lamH ∧ lamH < 1) ∧
    (lamL < M.shareHigh kh piHat ∧ lamL < M.shareHighHat kh kl piHat ∧ lamL < lamH) ∧
    -- the high type does not mimic the low type
    M.mfrProfit DemandType.h (M.optWe lamL) (M.optWo lamL) kl
      < M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    -- the low type does not mimic the high type
    M.mfrProfit DemandType.l (M.optWe lamH) (M.optWo lamH) kh
      ≤ M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl ∧
    -- the supplier's participation
    M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl = piHat ∧
    piHat ≤ M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    (M.shareHigh kh piHat ≤ M.shareHighHat kh kl piHat →
      M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh = piHat) ∧
    -- coordination: each type's initial order is optimal for her and for the supplier
    IsMaxOn (fun q => M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh ∧
    IsMaxOn (fun q => M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh := by sorry

end CachonCoord.CapacityForecast
