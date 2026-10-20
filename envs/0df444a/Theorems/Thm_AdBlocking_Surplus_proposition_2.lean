-- Prove2me | Theorems.Thm_AdBlocking_Surplus_proposition_2
-- name    : AdBlocking.Surplus.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:07.889089+00:00
-- url     : https://prove2.me/theorems/7d51a98c-9711-4e79-bd6c-e2b5228765c2
-- title:
--   Proposition 2 — lower quality and profit with an adblocker
-- statement:
--   There is a positive function $G(r,t)$ such that, once $\bar\kappa$ is sufficiently large, every benchmark-optimal ad selection and every adblocker best-response selection give a unique publisher-optimal quality $q^*_{AB}$, with the two-branch formula of Proposition 2:
--
--   $$q^*_{AB}=\begin{cases}\left[4c(1+r)(1-t)/p_a+G(r,t)/\bar\kappa\right]^{-1},&t\le r/(1+r),\\ \left[4c/(p_a(1-r(1-t)+t))+G(r,t)/\bar\kappa\right]^{-1},&t>r/(1+r).\end{cases}$$
--
--   This quality is below $q^*_{NA}$, increases strictly with $\bar\kappa$, and converges to $q^*_{NA}$ as $\bar\kappa\to\infty$. The publisher's equilibrium profit is below the benchmark profit and increases strictly with $\bar\kappa$. The quality reduction is the indirect cost to consumers in Proposition 3.
--
--   **Formalization Note** The support threshold may depend on $p_a,c,r,t$. The comparison quantifies over all maximizing selections, so it does not assume the closed-form qualities as hypotheses.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 18 (PDF 19), Proposition 2; pp. 42–43 (PDF 43–44), proof and equation (10)

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model
import Definitions.Def_AdBlocking_Surplus_ClosedForms

open Filter Topology

namespace AdBlocking.Surplus

theorem proposition_2 :
    ∃ G : ℝ → ℝ → ℝ,
      (∀ r t : ℝ, 0 < r → r ≤ 1 → 0 ≤ t → t ≤ 1 → 0 < G r t) ∧
      ∀ pa c r t : ℝ, Standing pa c r t →
        ∃ K : ℝ, 0 < K ∧
          (∀ κbar : ℝ, K ≤ κbar →
            ∀ (Asel Vsel : ℝ → ℝ),
              (∀ q : ℝ, 0 ≤ q → IsBenchAdBest pa r t q (Asel q)) →
              (∀ q : ℝ, 0 ≤ q → IsAdblockBest pa r t κbar q (Asel q) (Vsel q)) →
              (∀ q : ℝ, 0 ≤ q →
                (IsABEq pa c r t κbar Asel Vsel q ↔
                  q = abQualityStar pa c r t κbar (G r t))) ∧
              abQualityStar pa c r t κbar (G r t) < benchQualityStar pa c r t ∧
              pubProfitAB pa c r t κbar
                  (abQualityStar pa c r t κbar (G r t))
                  (Asel (abQualityStar pa c r t κbar (G r t)))
                  (Vsel (abQualityStar pa c r t κbar (G r t))) <
                benchProfit pa c r t Asel (benchQualityStar pa c r t)) ∧
          (∀ κbar₁ κbar₂ : ℝ, K ≤ κbar₁ → κbar₁ < κbar₂ →
            abQualityStar pa c r t κbar₁ (G r t) <
              abQualityStar pa c r t κbar₂ (G r t)) ∧
          Tendsto (fun κbar => abQualityStar pa c r t κbar (G r t)) atTop
            (𝓝 (benchQualityStar pa c r t)) ∧
          (∀ κbar₁ κbar₂ : ℝ, K ≤ κbar₁ → κbar₁ < κbar₂ →
            ∀ (Asel Vsel₁ Vsel₂ : ℝ → ℝ),
              (∀ q : ℝ, 0 ≤ q → IsBenchAdBest pa r t q (Asel q)) →
              (∀ q : ℝ, 0 ≤ q →
                IsAdblockBest pa r t κbar₁ q (Asel q) (Vsel₁ q)) →
              (∀ q : ℝ, 0 ≤ q →
                IsAdblockBest pa r t κbar₂ q (Asel q) (Vsel₂ q)) →
              pubProfitAB pa c r t κbar₁
                  (abQualityStar pa c r t κbar₁ (G r t))
                  (Asel (abQualityStar pa c r t κbar₁ (G r t)))
                  (Vsel₁ (abQualityStar pa c r t κbar₁ (G r t))) <
                pubProfitAB pa c r t κbar₂
                  (abQualityStar pa c r t κbar₂ (G r t))
                  (Asel (abQualityStar pa c r t κbar₂ (G r t)))
                  (Vsel₂ (abQualityStar pa c r t κbar₂ (G r t)))) := by sorry

end AdBlocking.Surplus
