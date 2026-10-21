-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law
-- name    : AvramDividend.Classical.chat04_levy_random_state_increment_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:20:44.162562+00:00
-- url     : https://prove2.me/theorems/53b4d2eb-ef57-4c07-af33-8872d18e1dfd
-- title:
--   The random Lévy reserve and future increment have a product joint law
-- statement:
--   For a spectrally negative Lévy process and any deterministic 0≤s≤t, the joint distribution of the random current state X_s and the future increment X_t−X_s is precisely the product of the law of X_s and the law of X_(t−s). This is the full random-state independence and stationary-increment Markov coupling. Derive it from the full past-filtration independence field, adaptedness of X_s, stationary increments, and pinned Mathlib IndepFun.map_prod_eq_prod_map_map. It provides the exact distributional foundation for transition-kernel integration with a random current reserve; no killed process, q-scale harmonicity or optional stopping is assumed.
-- source:
--   Official SpectrallyNegativeLevy indepIncrements, stationaryIncrements, adapted; exact Mathlib ProbabilityTheory.IndepFun_iff_Indep, ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map, IdentDistrib.map_eq at pinned 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_levy_random_state_increment_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map
        (fun ω => (X.X s ω, X.X t ω - X.X s ω)) P =
      (Measure.map (X.X s) P).prod (Measure.map (X.X (t - s)) P) := by sorry
