-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_time_state_future_product_of_cylinders
-- name    : AvramDividend.Classical.finite_time_state_future_product_of_cylinders
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:04:57.246032+00:00
-- url     : https://prove2.me/theorems/143aac01-c41d-42b8-a00e-3e4bc567b6a6
-- title:
--   Finite-time product law for arbitrary history and the whole shifted future path
-- statement:
--   For a spectrally negative Levy process at deterministic time s, let H be any F_s-measurable historical state. Assume the uniform finite-cylinder independence: every finite family of shifted future increments generates a sigma-algebra independent of the past filtration at s. Then the joint law of the pair (history, whole shifted future path) under P is exactly the product of the law of H and the law of the whole shifted future path. This generalizes the proved reserve-only product law (which fixes H to the current reserve X_s) to arbitrary stopped-history states, and is the deterministic-time bridge toward a finite-valued stopping-time Markov factorization for the barrier dividend value.
-- source:
--   Isolates the deterministic-time product-law step of the finite-grid stopping-time route to barrierStrategy_value_eq_killed_exit_mul_supValue. Generalizes Proved chat04_full_future_path_reserve_product_law from the reserve X_s to arbitrary F_s-measurable H. A complete source draft exists in-catalogue-review (research file finite_time_state_future_product_for_barrier_factorization.lean); this proposal publishes the statement only.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_time_state_future_product_of_cylinders
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P) :
    Measure.map
      (fun ω => (H ω,
        fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (fun ω => fun t : ℝ≥0 =>
          X.X (s + t) ω - X.X s ω) P) := by sorry
