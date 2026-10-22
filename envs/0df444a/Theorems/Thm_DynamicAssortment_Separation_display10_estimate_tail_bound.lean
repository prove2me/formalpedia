-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_display10_estimate_tail_bound
-- name    : DynamicAssortment.Separation.display10_estimate_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:49:46.761203+00:00
-- url     : https://prove2.me/theorems/94218048-b87c-4f2f-b352-93b2d5c05b77
-- title:
--   Display (10) (p. 402) — ℙ{‖μ − μ̂_t‖_{A_j} > ϵ, T^j(t) ≥ n} ≤ 2|A_j| exp(−c n) under Algorithm 1
-- statement:
--   In the setting of Theorem 2, let $\mathbb P$ be the law of the purchase history under Algorithm 1 with parameter $\kappa_1>0$ and horizon $T$. For every $\epsilon>0$ there is a constant $c>0$ such that, for every $\kappa_1>0$, every $T$, every customer $t<T$, every $n\ge1$ and every test assortment $A_j$,
--   $$\mathbb P\big\{\|\mu-\hat\mu_t\|_{A_j}>\epsilon,\ T^j(t)\ge n\big\}\le 2|A_j|\exp(-c\,n),$$
--   where $\hat\mu_t$ is the estimate computed from the customers before $t$ and $T^j(t)$ the number of those customers offered $A_j$.
--
--   It bounds the probability that the separation-based estimate of the mean utilities of a test assortment is off by more than $\epsilon$, after that assortment has been offered $n$ times.
--
--   **Formalization Note** The page's constant is $c(\epsilon/\kappa(\epsilon))$ with $c$ from Lemma 1 and $\kappa$ from (9); here it is an existential constant, quantified before $\kappa_1$, $T$, $t$, $n$ and $j$, so it does not depend on them. Line (b) of the page's chain writes $\sum_{s=1}^{t}(Z_i^s-p_i(A_j,\mu))\mathbf 1\{S_t=A_j\}$ for the sum over the earlier customers $\sum_{u<t}(\cdots)\mathbf 1\{S_u=A_j\}$, which is what the definition of $\hat p_{i,t}$ gives; the conclusion is unaffected.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 402, App. A, proof of Theorem 2, Step 1, display (10)

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
import Definitions.Def_DynamicAssortment_Separation_AssumptionOne

namespace DynamicAssortment.Separation

/-- Display (10) (App. A, p. 402): under Algorithm 1, for every `ε > 0` there is `c > 0`
(not depending on `κ₁`, `T`, `t`, `n`) with
`ℙ{‖μ - μ̂_t‖_{A_j} > ε, T^j(t) ≥ n} ≤ 2 |A_j| exp(-c n)` for every `n ≥ 1`. -/
theorem display10_estimate_tail_bound {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (hid : Identifiability f C eta) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ κ₁ : ℝ, 0 < κ₁ → ∀ T t n : ℕ, t < T → 1 ≤ n →
      ∀ j < numTests N C,
        prob f μ (algorithm1 C opt eta κ₁ T) (fun h =>
            ε < normOn (testAssortment N C j)
                (μ - muHat C eta (offeredSeq (algorithm1 C opt eta κ₁ T) h) (histSeq h) t) ∧
              n ≤ visitCount (offeredSeq (algorithm1 C opt eta κ₁ T) h) (testAssortment N C j) t)
          ≤ 2 * ((testAssortment N C j).card : ℝ) * Real.exp (-(c * n)) := by sorry

end DynamicAssortment.Separation
