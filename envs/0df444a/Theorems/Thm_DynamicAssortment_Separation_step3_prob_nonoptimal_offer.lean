-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_step3_prob_nonoptimal_offer
-- name    : DynamicAssortment.Separation.step3_prob_nonoptimal_offer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:49:37.300706+00:00
-- url     : https://prove2.me/theorems/01aae7e6-d3ef-48a7-a04a-35f5cbac2ef8
-- title:
--   Step 3 (pp. 402–403) — in the exploitation phase, ℙ{NO(t)} ≤ Σ_{A_j ∈ 𝒜} 2|A_j| T^{−κ₁ c}
-- statement:
--   In the setting of Theorem 2, let $\mathbb P$ be the law of the purchase history under Algorithm 1 with parameter $\kappa_1>0$ and horizon $T$, and let $NO(t)=\{S_t\neq S^*(\mu)\}$ be the event that customer $t$ is offered a nonoptimal assortment. There is a constant $c>0$ such that, for every $\kappa_1>0$, every $T$ and every exploitation-phase customer $t$, i.e. $|\mathcal A|\lceil\kappa_1\log T\rceil\le t<T$ with 0-based $t$,
--   $$\mathbb P\{NO(t)\}\le\sum_{A_j\in\mathcal A}2|A_j|\,T^{-\kappa_1 c}.$$
--
--   The page's constant is $c=c(\xi/\kappa(\xi))$ with $\xi=(2\|w\|_\infty KC)^{-1}\delta(\mu)r(S^*(\mu),\mu)$. This bound, summed over the exploitation phase, gives the constant term $\bar K_1$ of Theorem 2.
--
--   **Formalization Note** The constant $c$ is quantified before $\kappa_1$ and $T$. The page writes the range as "$t\ge|\mathcal A|\lceil\kappa_1\log T\rceil$" (1-based). That includes the last exploration customer, who is offered a test assortment regardless of the data. The statement is made for the exploitation phase, the range over which the proof sums ($t>|\mathcal A|\lceil\kappa_1\log T\rceil$ in 1-based indexing).
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, pp. 402–403, App. A, proof of Theorem 2, Step 3, display bounding ℙ{NO(t)}

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
import Definitions.Def_DynamicAssortment_Separation_AssumptionOne

namespace DynamicAssortment.Separation

/-- Step 3 of the proof of Theorem 2 (App. A, pp. 402–403): there is `c > 0` (not depending on
`κ₁` or `T`) such that every exploitation-phase customer `t` (0-based `t ≥ |𝒜| ⌈κ₁ log T⌉`)
is offered a nonoptimal assortment with probability
`ℙ{NO(t)} ≤ ∑_{A_j ∈ 𝒜} 2 |A_j| T^{-κ₁ c}`. -/
theorem step3_prob_nonoptimal_offer {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (hid : Identifiability f C eta) :
    ∃ c : ℝ, 0 < c ∧ ∀ κ₁ : ℝ, 0 < κ₁ → ∀ T t : ℕ,
      numTests N C * ⌈κ₁ * Real.log T⌉₊ ≤ t → t < T →
        prob f μ (algorithm1 C opt eta κ₁ T)
            (fun h => offeredSeq (algorithm1 C opt eta κ₁ T) h t ≠ opt μ)
          ≤ ∑ j ∈ Finset.range (numTests N C),
              2 * ((testAssortment N C j).card : ℝ) * (T : ℝ) ^ (-(κ₁ * c)) := by sorry

end DynamicAssortment.Separation
