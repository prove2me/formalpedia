-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p99_critical_ratio
-- name    : CachonCoord.CapacityForecast.p99_critical_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:32.358662+00:00
-- url     : https://prove2.me/theorems/7808e409-c3d2-4e8e-9ad2-02be0700f386
-- title:
--   §6.10.2, p. 99 — Ω_θ is concave and k > 0 is optimal iff F̄_θ(k) = c_k/(r − c_p)
-- statement:
--   In the capacity procurement game, the supply chain's expected profit $\Omega_\theta(k) = (r - c_p)S_\theta(k) - c_k k$ is concave on $k \ge 0$, and a positive capacity $k$ maximizes $\Omega_\theta$ over $[0, \infty)$ if and only if it satisfies the newsvendor critical ratio
--   $$\bar F_\theta(k) = \frac{c_k}{r - c_p}, \qquad \bar F_\theta = 1 - F_\theta .$$
--
--   This identifies the optimal capacity $k_\theta^o$ and the benchmark profit $\Omega_\theta^o = \Omega_\theta(k_\theta^o)$ against which every contract of the section is measured.
--
--   **Formalization Note** The page assumes $k_\theta^o > 0$ (footnote 46); the characterization is stated for positive capacities. Concavity holds because $F_\theta$ is nondecreasing; no strict monotonicity of $F_\theta$ is assumed, so the optimal capacity need not be unique.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 99, the critical-ratio display and footnote 46

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 99, the critical-ratio display: `Ω_θ` is concave in
capacity, and a positive capacity `k` (footnote 46 assumes `k_θ° > 0`) is an optimal capacity,
i.e. maximizes `Ω_θ` over `k ≥ 0`, exactly when it satisfies the newsvendor critical ratio
`F̄_θ(k) = c_k / (r − c_p)`. -/
theorem p99_critical_ratio (M : Model) (θ : DemandType) :
    ConcaveOn ℝ (Set.Ici 0) (M.Omega θ) ∧
      ∀ k : ℝ, 0 < k →
        (IsMaxOn (M.Omega θ) (Set.Ici 0) k ↔ 1 - cdf (M.μ θ) k = M.ck / (M.r - M.cp)) := by sorry

end CachonCoord.CapacityForecast
