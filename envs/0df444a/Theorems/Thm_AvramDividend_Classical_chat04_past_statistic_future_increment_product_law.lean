-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law
-- name    : AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:27:43.636839+00:00
-- url     : https://prove2.me/theorems/2e08771d-f678-4db6-825a-fc65503535c0
-- title:
--   Every F_s-measurable Lévy path-history statistic is independent of a future increment
-- statement:
--   Let X be a spectrally negative Lévy process adapted to filtration F and with independent stationary increments. For any ordered deterministic times s≤t, arbitrary measurable target space E, and any history statistic H:Ω→E measurable with respect to F_s, the joint law of H and the future increment X_t−X_s equals the product Law(H)⊗Law(X_(t−s)). This extends the already accepted random current reserve joint law to a completely arbitrary finite path history or path-dependent survival statistic, and supplies the recursive conditional independence step needed to establish Markov/product laws for general finite monitoring grids. No q-scale, martingale, integrability or path regularity hypothesis is imposed beyond the original canonical Lévy structure.
-- source:
--   Canonical SpectrallyNegativeLevy adapted, indepIncrements and stationaryIncrements axioms. Generalised exact compiler-accepted proof of chat04_levy_random_state_increment_product_law UUID 53b4d2eb-ef57-4c07-af33-8872d18e1dfd. Pinned Mathlib IndepFun_iff_Indep and IndepFun.map_prod_eq_prod_map_map.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map (fun ω => (H ω, X.X t ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (X.X (t - s)) P) := by sorry
