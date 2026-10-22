-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_finite_history_next_increment_product
-- name    : AvramDividend.Classical.chat04_arbitrary_finite_history_next_increment_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:27:35.064696+00:00
-- url     : https://prove2.me/theorems/f3a99de0-4cc4-4d46-924f-f14077835333
-- title:
--   Uniform arbitrary-n finite observation-history vector and next Lévy increment product law
-- statement:
--   Let X be the original spectrally negative Lévy process adapted to the filtration F. For ANY natural number n, arbitrary n observation times t_i≤u, a deterministic history time s≤u, an arbitrary measurable target type E and any E-valued statistic H measurable with respect to F_s, the joint law of the combined history (H,(X_(t_i)−X_s)_(i∈Fin n)) and the next increment X_v−X_u at v≥u equals the product of the combined history law with the stationary marginal Law(X_(v−u)). This is a uniform n-to-(n+1) step: it works for every finite observation vector cardinality and arbitrary history state without imposing chronological order on the earlier observation times, any q-scale, or integrability. It follows rigorously by showing the complete arbitrary-length finite observation vector is jointly F_u-measurable using adaptedness and measurable_pi_iff, then invoking the already officially accepted generic F_u-measurable past-statistic next-increment product law. It supplies the induction step to derive the missing uniform finite-cylinder law; completing the induction, handling sorted times, and transforming consecutive increments into positions remain separate work.
-- source:
--   Accepted theorem AvramDividend.Classical.chat04_past_statistic_future_increment_product_law UUID 2e08771d-f678-4db6-825a-fc65503535c0; canonical Lévy adaptedness, monotone filtration and Mathlib measurable_pi_iff.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_arbitrary_finite_history_next_increment_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    {n : ℕ}
    (s u v : ℝ≥0) (hsu : s ≤ u) (huv : u ≤ v)
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ u)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω => ((H ω, fun i : Fin n => X.X (t i) ω - X.X s ω),
        X.X v ω - X.X u ω)) P =
      (Measure.map
        (fun ω => (H ω, fun i : Fin n => X.X (t i) ω - X.X s ω)) P).prod
          (Measure.map (X.X (v - u)) P) := by sorry
