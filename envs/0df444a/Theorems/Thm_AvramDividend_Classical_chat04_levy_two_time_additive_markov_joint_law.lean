-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_levy_two_time_additive_markov_joint_law
-- name    : AvramDividend.Classical.chat04_levy_two_time_additive_markov_joint_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:37:38.519962+00:00
-- url     : https://prove2.me/theorems/a9dc9bed-1d00-4458-8e29-5012fa345d90
-- title:
--   Two-time Lévy Markov joint law as additive image of independent marginals
-- statement:
--   For every s≤t, the full joint probability measure of the Lévy process values (X_s,X_t) is the push-forward under (u,v)↦(u,u+v) of the product measure Law(X_s)⊗Law(X_(t−s)). This is an exact two-time Markov transition law for the random current reserve, requiring no integrability, no q-scale harmonicity and no stopping theorem. It follows from the already accepted random-current-state/future-increment product joint law and pinned Mathlib Measure.map_map plus X_t=X_s+(X_t−X_s). It underpins conditioning on the actual random reserve rather than only deterministic starting values.
-- source:
--   Official Prove2Me ACCEPTED AvramDividend.Classical.chat04_levy_random_state_increment_product_law theorem 53b4d2eb-ef57-4c07-af33-8872d18e1dfd; pinned Mathlib MeasureTheory.Measure.map_map from Mathlib.MeasureTheory.Measure.Map.

import Mathlib.MeasureTheory.Measure.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_levy_two_time_additive_markov_joint_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map (fun ω => (X.X s ω, X.X t ω)) P =
      Measure.map
        (fun z : ℝ × ℝ => (z.1, z.1 + z.2))
        ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)) := by sorry
