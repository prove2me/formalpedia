-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_full_future_path_product_law
-- name    : AvramDividend.Classical.chat04_arbitrary_history_full_future_path_product_law
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T08:00:42.227141+00:00
-- url     : https://prove2.me/theorems/df53d7ad-ff31-4809-8a72-f7b90798838e
-- title:
--   Joint law of arbitrary past statistic and whole shifted future Lévy path is a product measure
-- statement:
--   For a canonical spectrally negative Lévy process X, deterministic time s, arbitrary measurable E-valued statistic H of the full history F_s, assume joint independence of each finite-dimensional vector of future shifted increments (X_(s+t)−X_s) for every finite set of t≥0 from H. Then the WHOLE joint law of (H, full shifted future trajectory (t↦X_(s+t)−X_s)) is the product of the history's marginal law and the complete shifted future process's marginal law, as measures on E×(nonnegative-time→real). The proof applies the already officially ACCEPTED full-path independence from finite cylinders to H, shows measurability of the full process by adaptedness and measurable_pi_iff, and applies pinned Mathlib IndepFun.map_prod_eq_prod_map_map after symmetry. This supplies a real path-space Markov kernel needed to evaluate killed future-survival rewards jointly with the current reserve and arbitrary previous path-history, and extends the previously accepted one-, two-, and three-increment product laws. The uniform finite-cylinder independence premise remains explicit and must still be proved from the original Lévy axioms. This result does not establish killed q-harmonicity.
-- source:
--   Officially ACCEPTED AvramDividend.Classical.chat04_full_shifted_future_path_indep_of_all_finite_cylinders UUID 7b8aa9ab-9dc6-4b9a-a595-32d384e805ca and Mathlib ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map, original Lévy adaptedness.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_indep_of_all_finite_cylinders

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_arbitrary_history_full_future_path_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      IndepFun
        (fun ω (i : I) => X.X (s + (i : ℝ≥0)) ω - X.X s ω)
        H P) :
    Measure.map
      (fun ω => (H ω,
        (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω))) P =
      (Measure.map H P).prod
        (Measure.map
          (fun ω => (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P) := by sorry
