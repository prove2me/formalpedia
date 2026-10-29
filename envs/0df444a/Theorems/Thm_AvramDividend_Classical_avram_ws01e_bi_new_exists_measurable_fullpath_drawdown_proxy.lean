-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:52:08.764176+00:00
-- url     : https://prove2.me/theorems/38b6f34a-08f7-4b50-942d-773c565900b8
-- title:
--   Existence of a jointly measurable countable full-path drawdown proxy with genuine fresh and shifted Lévy identities
-- statement:
--   There exists a real-valued product-Pi measurable function of an arbitrary nonnegative clock and entire path, constructed from dyadic ceiling Cantor-prefix reward limsup, which equals the actual running-supremum terminal drawdown on every genuine Levy path and every centred time-shifted Levy path. This existential format avoids a separate public definition while retaining exactly the Borel-measurable test required by genuine Esscher Qp regeneration.
-- source:
--   Exact accepted dyadic reward joint measurability 46658681, fresh-path convergence 5886c047, shifted path limsup equality 91c5d4c8, and exponential/logarithm inversion. No independence premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ F : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
      Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => F z.1 z.2) ∧
      (∀ (ω : Ω) (t : ℝ≥0),
        F t (fun s : ℝ≥0 => X.X s ω) =
          runningSup X t ω - X.X t ω) ∧
      (∀ (ω : Ω) (u t : ℝ≥0),
        F t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
          sSup ((fun v : ℝ≥0 =>
            X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
            (X.X (u + t) ω - X.X u ω)) := by sorry
