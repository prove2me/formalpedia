-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:42:59.789799+00:00
-- url     : https://prove2.me/theorems/12d8da1c-361c-4552-93ec-b50d737c914e
-- title:
--   One genuine measurable countable drawdown test equals fresh and every shifted Lévy drawdown
-- statement:
--   An explicit countably sampled dyadic-ceiling drawdown exponential reward H, defined by its ENNReal limsup on arbitrary path functions, is measurable on the unrestricted product of nonnegative time and the Pi-function path space. For the actual spectrally negative Lévy process, for every sample path and horizon H equals the terminal exponential of the genuine running-supremum drawdown, and for every shifted age and residual horizon H equals the exponential of the actual shifted centred-path drawdown. These are simultaneous pointwise facts, without an exceptional set, so H can be instantiated in the accepted genuine Qp upper-record full-path regeneration theorem.
-- source:
--   Canonical Proved genuine unshifted Cantor drawdown convergence 5886c047; genuine shifted Cantor drawdown convergence 20ea0d9b; product-Pi dyadic reward measurability 46658681; pinned Mathlib Measurable.limsup and Filter.Tendsto.limsup_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (β : ℝ) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun t f =>
       Filter.limsup (fun n : ℕ =>
         let r : ℝ≥0 :=
           (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
         ENNReal.ofReal (Real.exp
           (-β * ((⨆ i : ℕ, if samples i ≤ r then
             ENNReal.ofReal (f (samples i)) else 0).toReal - f r))))
       Filter.atTop
     Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) ∧
       (∀ (ω : Ω) (t : ℝ≥0),
         H t (fun s : ℝ≥0 => X.X s ω) =
           ENNReal.ofReal (Real.exp
             (-β * (runningSup X t ω - X.X t ω)))) ∧
       (∀ (ω : Ω) (u t : ℝ≥0),
         H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
           ENNReal.ofReal (Real.exp (-β *
             (sSup ((fun v : ℝ≥0 =>
               X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
               (X.X (u + t) ω - X.X u ω)))))) := by sorry
