-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
-- name    : AvramDividend.Classical.countable_pastSup_adapted_of_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:10:39.982682+00:00
-- url     : https://prove2.me/theorems/e543ab50-fbe6-414b-82ed-42eca681cbfd
-- title:
--   Countably sampled running supremum is adapted for any adapted real-valued continuous-time process
-- statement:
--   For any adapted real-valued process u and any countable set S of nonnegative observation times, its past supremum over observations s in S satisfying s≤t is adapted. Each observation is filtration-t measurable using hu and filtration monotonicity, and the sampled index subtype is countable. Apply Mathlib Measurable.iSup. Generalises the accepted countable_pastSup_adapted theorem for X itself and applies to the actual reflected Lévy drawdown process. This is the key measurability step in representing continuous-time compact-prefix suprema through dense samples plus the endpoint.
-- source:
--   Exact accepted Prove2Me countable_pastSup_adapted proof candidate 282cd0ee-cf03-461b-aec6-6d6d2e9c0904, generalised from X.adapted to arbitrary hu.

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.countable_pastSup_adapted_of_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (u : ℝ≥0 → Ω → ℝ) (hu : Adapted 𝓕 u)
    (S : Set ℝ≥0) (hS : S.Countable) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, u s.1 ω) := by sorry
