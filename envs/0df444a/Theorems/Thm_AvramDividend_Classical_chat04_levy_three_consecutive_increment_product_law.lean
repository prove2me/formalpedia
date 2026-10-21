-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_levy_three_consecutive_increment_product_law
-- name    : AvramDividend.Classical.chat04_levy_three_consecutive_increment_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:45:46.070805+00:00
-- url     : https://prove2.me/theorems/adf6e5bb-a491-49b4-88bc-4836ec017ebd
-- title:
--   Three consecutive Lévy state and increment components have the product joint law
-- statement:
--   For any ordered deterministic times 0≤s≤t≤u in the canonical spectrally negative Lévy model, the full three-component joint law of X_s, X_t−X_s and X_u−X_t equals the nested product of Law(X_s), Law(X_(t−s)), and Law(X_(u−t)). The key nontrivial step is measurability of the first state and first future increment with respect to F_t. The official independent-increments axiom at t makes the second future increment independent of that entire pair. The accepted two-component random-state joint law and stationary increments identify the component marginals. This is a rigorous two-step finite-grid stochastic Markov/path input for eventual pathwise first-passage and killed semigroup reasoning; the killed q-scale martingale remains open.
-- source:
--   Official SpectrallyNegativeLevy.adapted, indepIncrements, stationaryIncrements; accepted Chat04 random-state/future-increment product joint law UUID 53b4d2eb-ef57-4c07-af33-8872d18e1dfd; pinned Mathlib Filtration.mono and IndepFun.map_prod_eq_prod_map_map.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_levy_three_consecutive_increment_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    Measure.map
      (fun ω => ((X.X s ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω)) P =
      ((Measure.map (X.X s) P).prod
        (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P) := by sorry
