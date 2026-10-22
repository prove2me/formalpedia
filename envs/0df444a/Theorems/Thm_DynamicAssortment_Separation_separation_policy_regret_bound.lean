-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_separation_policy_regret_bound
-- name    : DynamicAssortment.Separation.separation_policy_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:49:57.988181+00:00
-- url     : https://prove2.me/theorems/0268e3b9-581b-4e97-8f44-eecd4d3bd659
-- title:
--   Theorem 2 (p. 394) — the separation-based policy π₁ has regret at most κ₁⌈N/C⌉ log T + K̄₁ for all T, provided κ₁ > κ̄₁
-- statement:
--   Consider a retailer with $N$ products, display capacity $1\le C\le N$, margins $w_i>0$, and customers with random utilities $U_i=\mu_i+\zeta_i$ ($\mu_0=0$), whose shocks have an everywhere-positive density. Suppose the single-sale problem (1) has a unique solution at the true mean-utility vector $\mu$, and let $S^*(\cdot)$ be a selection of its maximizers at every vector. Let Assumption 1 hold with inverse $\eta$.
--
--   For $\kappa_1>0$ and horizon $T$, let $\pi_1=\pi(\kappa_1,T,w)$ be Algorithm 1: offer each of the $\lceil N/C\rceil$ test assortments to $\lceil\kappa_1\log T\rceil$ customers, then offer $S^*(\hat\mu_t)$ to every remaining customer, where $\hat\mu_t$ is $\eta$ applied to the empirical purchase frequencies (4). Then there exist finite constants $\bar K_1$ and $\bar\kappa_1$, which depend on the instance but not on $T$ or $\kappa_1$, such that
--   $$\mathcal R^{\pi_1}(T,\mu)\le\kappa_1\lceil N/C\rceil\log T+\bar K_1\qquad\text{for all }T,$$
--   provided $\kappa_1>\bar\kappa_1$.
--
--   The theorem shows that a policy which separates exploration from exploitation, and tests every product for order-$\log T$ customers, achieves regret of order $\lceil N/C\rceil\log T$, the rate in $T$ of the paper's lower bound (Theorem 1).
--
--   **Formalization Note** The constants $\bar K_1,\bar\kappa_1$ are existential and come after the instance data and before $\kappa_1$ and $T$. $\log$ is the natural logarithm, $\log 0=\log 1=0$, and $\lceil N/C\rceil$ is computed as $(N+C-1)/C$ in $\mathbb N$. Several hypotheses are standing assumptions of the paper that the theorem's sentence does not repeat: $w_i>0$ and $C\le N$ (§3.1); $\mu_0=0$ and uniqueness of the optimum (§3.2); a positive density (§4.1). $1\le C$ is implicit on the page, since otherwise $r(S^*(\mu),\mu)=0$ and the regret divides by zero. Assumption 1 is used in its per-test-assortment form, with Lipschitz continuity of every $p(S,\cdot)$, $S\in\mathcal S$ (see `AssumptionOne`). The estimator is the paper's, $\eta$ applied to (4), not an oracle.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 394, Theorem 2 (proof in App. A, pp. 402–403)

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
import Definitions.Def_DynamicAssortment_Separation_AssumptionOne

namespace DynamicAssortment.Separation

/-- Theorem 2 (p. 394): for Algorithm 1 under Assumption 1 there are finite constants `K̄₁`, `κ̄₁`
(depending on the instance only, not on `T` or `κ₁`) such that
`ℛ^{π₁}(T, μ) ≤ κ₁ ⌈N/C⌉ log T + K̄₁` for all `T`, whenever `κ₁ > κ̄₁`. -/
theorem separation_policy_regret_bound {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (hid : Identifiability f C eta) :
    ∃ Kbar₁ κbar₁ : ℝ, ∀ κ₁ : ℝ, 0 < κ₁ → κbar₁ < κ₁ → ∀ T : ℕ,
      regret f w μ (opt μ) (algorithm1 C opt eta κ₁ T) ≤
        κ₁ * (numTests N C : ℝ) * Real.log T + Kbar₁ := by sorry

end DynamicAssortment.Separation
