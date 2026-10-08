-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_eq_27
-- name    : CachonCoord.DemandUpdate.eq_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:50.084512+00:00
-- url     : https://prove2.me/theorems/d90b2f13-cfcc-4773-8b24-2bc9a767d72f
-- title:
--   Eq. (27), p. 66 — ∂Ω₁/∂q₁ = −c₁ + c₂(1 − G(ξ(q₁))) + ∫₀^{ξ(q₁)} pS′(q₁|ξ)g(ξ)dξ, zero at q₁°
-- statement:
--   Let $q_2(q_1,\xi)$ be a supply chain optimal period-2 order. At every $q_1 > 0$ for which Eq. (26) has a solution $\xi(q_1) \ge 0$, the supply chain's expected profit $\Omega_1$ is differentiable with
--   $$\frac{\partial \Omega_1(q_1)}{\partial q_1} = -c_1 + c_2\big(1 - G(\xi(q_1))\big) + \int_0^{\xi(q_1)} p\,S'(q_1\,|\,\xi)\,g(\xi)\,d\xi,$$
--   where $S'(q\,|\,\xi) = 1 - F(q\,|\,\xi)$. At a supply chain optimal period-1 order $q_1^o > 0$ (a maximizer of $\Omega_1$ over $q_1 \ge 0$) this derivative vanishes, which is (27).
--
--   Eq. (27) is the first-order condition of the supply chain's period-1 problem. It is also the input to the supplier's period-1 production decision on p. 67.
--
--   **Formalization Note** $S'$ is written out as $1 - F$. The page's "given $\Omega_1$ is strictly concave" is needed only for the first-order condition to be sufficient; the necessary condition stated here holds without it. Existence of $\xi(q_1)$ is a hypothesis, as on the page.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, Eq. (27), p. 66

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, Eq. (27), p. 66. Let `q2sel` select a supply chain optimal
period-2 order `q_2(q_1, ξ)`. At every `q_1 > 0` for which (26) has a solution `ξ(q_1) = xi1 ≥ 0`,
`Ω_1` is differentiable with
`∂Ω_1(q_1)/∂q_1 = −c_1 + c_2(1 − G(ξ(q_1))) + ∫_0^{ξ(q_1)} pS'(q_1|ξ) g(ξ) dξ`, where
`S'(q|ξ) = 1 − F(q|ξ)`; and at a supply chain optimal `q_1° > 0` this derivative is `0`. -/
theorem eq_27 (M : Model) (q2sel : ℝ → ℝ → ℝ) (hq2 : M.IsChainPeriod2Optimal q2sel) :
    (∀ q1 xi1, 0 < q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio →
      HasDerivAt (M.Omega1 q2sel)
        (-M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1) * M.g ξ) q1) ∧
    (∀ q1o xi1, 0 < q1o → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1o →
      0 ≤ xi1 → M.F xi1 q1o = M.ratio →
      -M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1o) * M.g ξ = 0) := by sorry

end CachonCoord.DemandUpdate
