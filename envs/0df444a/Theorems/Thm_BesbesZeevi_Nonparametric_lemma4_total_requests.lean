-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_lemma4_total_requests
-- name    : BesbesZeevi.Nonparametric.lemma4_total_requests
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:50:49.568107+00:00
-- url     : https://prove2.me/theorems/0964f136-4350-4eed-b84c-6e094e9098f0
-- title:
--   Lemma 4: if $\lambda(\overline p)\le x/T$ then $\mathbb P(Y_n-nx>C_5nu_n)\le C_6/n^{\eta-1}$
-- statement:
--   Use the tuning of Proposition 1, with $\eta=2$. There are constants $C_5,C_6>0$, independent of the demand function and of $n$, with the following property.
--
--   Let $\lambda\in\mathcal L$ with $\lambda(\overline p)\le x/T$ (Case 1 of the proof of Proposition 1). Let $Y_n$ be the total number of requests of Algorithm 1 over the horizon, counted as if stock never ran out. Then for all $n\ge1$,
--
--   $$
--   \mathbb P\big(Y_n-nx>C_5\,n\,u_n\big)\le\frac{C_6}{n^{\eta-1}}.
--   $$
--
--   The total requests exceed the inventory by more than $O(nu_n)$ only with small probability.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 29 (PDF 31), Lemma 4, eq. (A-8); case hypothesis from Step 3, Case 1

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

/-- Lemma 4, p. 29 (Case 1 of Step 3, `λ(p̄) ≤ x/T`; `η = 2`): `P(Y_n - n x > C₅ n u_n) ≤ C₆/n^{η-1}`,
with constants independent of `λ ∈ 𝓛` and `n`. -/
theorem lemma4_total_requests (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₅ C₆ : ℝ, 0 < C₅ ∧ 0 < C₆ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ lam : ℝ → ℝ, L.Mem P lam → lam P.pu ≤ x / T →
        ∀ n : ℕ, 1 ≤ n →
          ℙ {ω | ((requestsTotal P lam x T n (τ n) (κ n) N ω : ℕ) : ℝ) - (n : ℝ) * x > C₅ * (n : ℝ) * uSeq n (τ n) (κ n)}
            ≤ ENNReal.ofReal (C₆ / (n : ℝ)) := by sorry

end BesbesZeevi.Nonparametric
