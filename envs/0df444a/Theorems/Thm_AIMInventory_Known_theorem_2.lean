-- Prove2me | Theorems.Thm_AIMInventory_Known_theorem_2
-- name    : AIMInventory.Known.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:54.438868+00:00
-- url     : https://prove2.me/theorems/7157b0de-867d-4249-ba21-8d00ba15a0d2
-- title:
--   Theorem 2 — AIM's average expected cost is within (γ+1/γ)ȳ max{b,h}/√T (perishable) and C/√T (non-perishable) of Q(y^NV)
-- statement:
--   Let demands $D_1, D_2, \dots \ge 0$ be i.i.d. with finite positive mean, let $h, b > 0$, and let $Q(y) = h\,E[y-D]^+ + b\,E[D-y]^+$ with newsvendor quantity
--   $$y^{NV} = \inf\{y \ge 0 \mid F(y) \ge b/(b+h)\},$$
--   $F$ the distribution function of $D_1$. Under Assumption 1 the manager knows $\bar y > 0$ with $y^{NV} \le \bar y$. Run the AIM algorithm with scale $\gamma > 0$ and any starting level $\hat y_1 \in [0,\bar y]$, and let $(y_t : t \ge 1)$ be its order-up-to levels. Then:
--
--   1. **Perishable inventory.** For every $T \ge 1$,
--   $$E\Big[\frac1T\sum_{t=1}^T Q(y_t)\Big] - Q(y^{NV}) \le \Big(\gamma + \frac1\gamma\Big)\frac{\bar y\max\{b,h\}}{\sqrt T}.$$
--   2. **Non-perishable inventory.** Suppose moreover that $0 < \rho < E[D_1]$ (the second half of Assumption 1), $E[D_1^6] < \infty$ and $\gamma \le \rho\max\{b,h\}/(h\bar y)$. Then there is a constant $C$ such that for every $T \ge 1$,
--   $$E\Big[\frac1T\sum_{t=1}^T Q(y_t)\Big] - Q(y^{NV}) \le \frac{C}{\sqrt T}.$$
--
--   The algorithm sees only censored sales and does not know the demand distribution, yet its long-run average cost approaches the newsvendor cost, which is the optimal cost of a manager who knows the distribution, at rate $1/\sqrt T$.
--
--   The constant $C$ may depend on everything except $T$. The paper's explicit formula (9) for $C$ rests on Proposition 4 (i), which is false as printed; with the corrected Proposition 4 (i) the same proof gives
--   $$C = \Big(\gamma + \frac1\gamma\Big)\bar y\max\{b,h\} + 2h\rho\Big(1 + \frac{21\pi^2}{2}\cdot\frac{E[(D_1-E D_1)^6]}{(E D_1 - \rho)^6}\Big).$$
--   This formula is not part of the statement.
--
--   **Formalization Note** The AIM run is defined from the demand path, and the expectation is the integral over the i.i.d. path law; the integrand is bounded on the run (all levels lie in $[0,\bar y]$), so the integral is a genuine expectation. $h, b, \bar y > 0$ are implicit in the paper (they appear in denominators), and the positive mean of $D_1$ is part of the reused demand-law structure (in the non-perishable case it already follows from $0 < \rho < E[D_1]$). In the non-perishable case the constant is chosen after $\rho$ and all other data, before $T$.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 7, Theorem 2 (with Assumption 1, p. 7; proof in §2.4, p. 10)

import Mathlib
import Definitions.Def_AIMInventory_Known_AIM
open MeasureTheory
open scoped NNReal

namespace AIMInventory.Known

/-- Theorem 2, p. 7: under Assumption 1 (`y^NV ≤ ȳ`), the AIM run satisfies, for every `T ≥ 1`,
`E[(1/T) Σ_{t=1}^T Q(y_t)] − Q(y^NV) ≤ (γ + 1/γ) ȳ max{b, h} / √T` in the perishable case; and
in the non-perishable case, if moreover `0 < ρ < E[D_1]`, `E[D_1^6] < ∞` and
`γ ≤ ρ max{b, h}/(hȳ)`, there is a constant `C` with
`E[(1/T) Σ_{t=1}^T Q(y_t)] − Q(y^NV) ≤ C / √T` for every `T ≥ 1`. -/
theorem theorem_2 (P : CappedBaseStock.DemandLaw) (h b γ ybar yhat1 : ℝ)
    (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ) (hybar : 0 < ybar)
    (hyhat1 : yhat1 ∈ Set.Icc 0 ybar)
    (hNV : ((LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ≥0) : ℝ) ≤ ybar) :
    (∀ T : ℕ, 1 ≤ T →
      avgExpectedCost P .perishable ybar γ b h yhat1 T
          - Q P h b (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)
        ≤ (γ + 1 / γ) * (ybar * max b h / Real.sqrt T)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < CappedBaseStock.mean P →
      Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 6) P.law →
      γ ≤ ρ * max b h / (h * ybar) →
      ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T →
        avgExpectedCost P .nonPerishable ybar γ b h yhat1 T
            - Q P h b (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)
          ≤ C / Real.sqrt T) := by sorry

end AIMInventory.Known
