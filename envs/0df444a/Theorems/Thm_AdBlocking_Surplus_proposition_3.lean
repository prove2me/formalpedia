-- Prove2me | Theorems.Thm_AdBlocking_Surplus_proposition_3
-- name    : AdBlocking.Surplus.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:53.682731+00:00
-- url     : https://prove2.me/theorems/f55c8aac-8228-4b39-adf5-304c7796b16f
-- title:
--   Proposition 3 — consumer-surplus comparison at equilibrium
-- statement:
--   In the paper's ad-blocking game, there is a positive tolerance $\varepsilon$ such that if either $0<r<\varepsilon$ or $0\le t<\varepsilon$, total consumer surplus at every adblocker equilibrium is below that at every benchmark equilibrium, provided the download-cost support $\bar\kappa$ is sufficiently large. There is also a positive tolerance $\delta$ such that if both $r$ and $t$ exceed $1-\delta$, the comparison reverses for all sufficiently large $\bar\kappa$:
--
--   $$CS_{AB}<CS_{NA}\quad\text{for sufficiently low }r\text{ or }t,\qquad
--     CS_{NA}<CS_{AB}\quad\text{when both }r,t\text{ are sufficiently high}.$$
--
--   The tolerances are uniform over the positive ad price and quality-cost coefficient. The threshold for $\bar\kappa$ may depend on those coefficients and on $r,t$. The result formalizes the paper's total-consumer-surplus comparison, including the opposing effects of lower ads and lower quality.
--
--   **Formalization Note** The page's “$\kappa$ high enough” is read as a bound on the population support $\bar\kappa$. Equilibria are defined by optimization of expectation-based payoffs, with the same benchmark-optimal ad level used in both regimes and the publisher paying all downloader ad revenue to the adblocker. No closed-form equilibrium quantity is substituted into this goal.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 20 (PDF 21), Proposition 3; pp. 43–44 (PDF 44–45), proof

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

namespace AdBlocking.Surplus

theorem proposition_3 :
    (∃ ε : ℝ, 0 < ε ∧ ∀ pa c r t : ℝ, Standing pa c r t →
      (r < ε ∨ t < ε) →
      ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
        ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
          IsBenchEq pa c r t Asel qN →
          IsABEq pa c r t κbar Asel Vsel qA →
          csAB r t κbar qA (Asel qA) (Vsel qA) <
            csNA r t qN (Asel qN)) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ pa c r t : ℝ, Standing pa c r t →
      1 - δ < r → 1 - δ < t →
      ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
        ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
          IsBenchEq pa c r t Asel qN →
          IsABEq pa c r t κbar Asel Vsel qA →
          csNA r t qN (Asel qN) <
            csAB r t κbar qA (Asel qA) (Vsel qA)) := by sorry

end AdBlocking.Surplus
