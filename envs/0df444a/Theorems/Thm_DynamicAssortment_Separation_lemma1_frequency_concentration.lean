-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_lemma1_frequency_concentration
-- name    : DynamicAssortment.Separation.lemma1_frequency_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:49:13.350978+00:00
-- url     : https://prove2.me/theorems/1652ef93-5e99-4fdc-b059-5e27140c3e2d
-- title:
--   Lemma 1 (p. 402) — exponential concentration of purchase frequencies on a test assortment under Algorithm 1
-- statement:
--   Consider the setting of Theorem 2: $1\le C\le N$, margins $w_i>0$, a positive noise density, an optimal-assortment selection $S^*$ that is unique at the true $\mu$, and an inverse $\eta$ satisfying Assumption 1. Let $\mathbb P$ be the law of the purchase history when Algorithm 1 is run with parameter $\kappa_1>0$ and horizon $T$.
--
--   Fix a test assortment $A_j$ and a product $i\in A_j$. For every $\epsilon>0$ there is a constant $c(\epsilon)>0$ such that, for every $\kappa_1>0$, every $T$, every customer $t<T$ and every $n\ge1$,
--   $$\mathbb P\Big\{\Big|\sum_{u<t}\big(Z_i^u-p_i(A_j,\mu)\big)\mathbf 1\{S_u=A_j\}\Big|\ge\epsilon\,T^j(t),\ T^j(t)\ge n\Big\}\le 2\exp(-c(\epsilon)\,n),$$
--   where $T^j(t)=\sum_{u<t}\mathbf 1\{S_u=A_j\}$ is the number of earlier customers offered $A_j$.
--
--   This is the concentration step of the proof of Theorem 2: once a test assortment has been offered $n$ times, its empirical purchase frequencies are within $\epsilon$ of the true ones except with probability exponentially small in $n$.
--
--   **Formalization Note** The constant $c(\epsilon)$ is quantified before $\kappa_1$, $T$, $t$ and $n$, so it does not depend on them; the proof of Theorem 2 needs exactly this uniformity. Customers are 0-based, so "$u<t$" is the paper's $u=1,\dots,t-1$. The proof of Lemma 1 is in the paper's online companion (Appendix D) and is not reproduced in the article.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 402, App. A, Lemma 1

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
import Definitions.Def_DynamicAssortment_Separation_AssumptionOne

namespace DynamicAssortment.Separation

/-- Lemma 1 (App. A, p. 402): under Algorithm 1, for a test assortment `A_j` and `i ∈ A_j`,
`ℙ{|∑_{u<t} (Z_i^u - p_i(A_j, μ)) 1{S_u = A_j}| ≥ ε T^j(t), T^j(t) ≥ n} ≤ 2 exp(-c(ε) n)`
for every `n ≥ 1`, with `c(ε) > 0` not depending on `κ₁`, `T`, `t` or `n`. -/
theorem lemma1_frequency_concentration {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (hid : Identifiability f C eta)
    (j : ℕ) (hj : j < numTests N C) (i : Fin N) (hi : i ∈ testAssortment N C j) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ κ₁ : ℝ, 0 < κ₁ → ∀ T t n : ℕ, t < T → 1 ≤ n →
      prob f μ (algorithm1 C opt eta κ₁ T) (fun h =>
          ε * (visitCount (offeredSeq (algorithm1 C opt eta κ₁ T) h) (testAssortment N C j) t : ℝ)
              ≤ |∑ u ∈ Finset.range t,
                  (purchased (histSeq h) u i - choiceProb f μ (testAssortment N C j) i) *
                    (if offeredSeq (algorithm1 C opt eta κ₁ T) h u = testAssortment N C j
                      then (1 : ℝ) else 0)| ∧
            n ≤ visitCount (offeredSeq (algorithm1 C opt eta κ₁ T) h) (testAssortment N C j) t)
        ≤ 2 * Real.exp (-(c * n)) := by sorry

end DynamicAssortment.Separation
