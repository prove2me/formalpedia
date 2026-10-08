-- Prove2me | Theorems.Thm_ChenBullwhip_Decentralized_eq_6
-- name    : ChenBullwhip.Decentralized.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:34:55.711927+00:00
-- url     : https://prove2.me/theorems/60e56465-cf6c-4e7a-a75f-1c7e1f34788f
-- title:
--   Eq. (6) — for i.i.d. demand, $\mathrm{Var}(q)/\mathrm{Var}(D) \ge 1 + 2L/p + 2L^2/p^2$
-- statement:
--   Let $D_t = \mu + \epsilon_t$ be i.i.d. demand, where the errors $\epsilon_t$ are independent and identically distributed from a symmetric distribution with mean $0$ and variance $\sigma^2 > 0$. Suppose the retailer uses the moving-average order-up-to policy $y_t = \hat D^L_t + z\,\hat\sigma^L_{et}$ of Eqs. (2)–(3) with $p \ge 1$ demand observations, lead time $L$, an arbitrary safety factor $z$ and an arbitrary constant $C_{L,\rho}$, and orders $q_t = y_t - y_{t-1} + D_{t-1}$. Then in every period $t$
--
--   $$\frac{\operatorname{Var}(q_t)}{\operatorname{Var}(D_t)} \;\ge\; 1 + \frac{2L}{p} + \frac{2L^2}{p^2}.$$
--
--   This is the case $\rho = 0$ of Theorem 2.2 (Eq. (5)) of Chen, Drezner, Ryan and Simchi-Levi (2000). With $z = 0$ it is the case $k = 1$ of Theorem 3.2: the retailer's orders are already more variable than the demand it faces, by an explicit factor depending only on $L/p$.
--
--   **Formalization Note** The hypothesis $p \ge 1$ is implicit in the paper (a moving average over $p$ observations). The demand model carries square integrability of the errors and $\sigma > 0$, so both variances are genuine and the ratio is well defined. $\mu$ carries no sign condition and $L \in \mathbb N$ may be $0$; neither affects the statement.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 439, §2.3, Eq. (6)

import Mathlib
import Definitions.Def_ChenBullwhip_Decentralized_IIDDemand
import Definitions.Def_ChenBullwhip_Decentralized_SingleStage

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Decentralized

/-- Eq. (6), §2.3: for i.i.d. symmetric demand and the moving-average order-up-to policy (2)–(3)
with `p ≥ 1` observations, lead time `L`, any safety factor `z` and any constant `C_{L,ρ} = C`,
`Var(qₜ)/Var(Dₜ) ≥ 1 + 2L/p + 2L²/p²`. -/
theorem eq_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : IIDDemand P) (p L : ℕ) (hp : 1 ≤ p) (C z : ℝ) (t : ℤ) :
    variance (X.order C z L p t) P / variance (X.D t) P
      ≥ 1 + 2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2 := by sorry

end ChenBullwhip.Decentralized
