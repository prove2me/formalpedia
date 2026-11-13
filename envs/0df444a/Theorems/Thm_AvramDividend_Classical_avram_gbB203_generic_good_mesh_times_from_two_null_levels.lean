-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB203_generic_good_mesh_times_from_two_null_levels
-- name    : AvramDividend.Classical.avram_gbB203_generic_good_mesh_times_from_two_null_levels
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:18:23.250274+00:00
-- url     : https://prove2.me/theorems/f8a722dd-7aec-47b9-ae11-986f78309137
-- title:
--   Two prescribed null spatial occupation levels imply almost-everywhere good clipping times for any random horizon
-- statement:
--   For a sample path continuous except at countably many times, and two fixed levels known to have zero finite-horizon time occupation, almost every physical time has a continuous path, avoids both levels and the random stop instant, and inherits derivative continuity inside the clipping band whenever the derivative is continuous throughout that band.
-- source:
--   General deterministic measurable-time core of original Gaussian B163 and B162, freed from the B100 fixed-level stochastic obligation; use B202 to select good cutoffs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB203_generic_good_mesh_times_from_two_null_levels
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (Y : ℝ≥0 → Ω → ℝ)
    (hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 | ¬ ContinuousAt
        (fun u : ℝ≥0 => Y u ω) s})
    (n : ℕ) (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hOccA : ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0)
    (hOccB : ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0)
    (w : ℝ → ℝ)
    (hDeriv : ∀ y ∈ Ioo a b, ContinuousAt (deriv w) y) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict
      (Ioo (0 : ℝ) (n : ℝ))),
      ContinuousAt (fun s : ℝ => Y (Real.toNNReal s) ω) t ∧
      Y (Real.toNNReal t) ω ≠ a ∧
      Y (Real.toNNReal t) ω ≠ b ∧
      t ≠ (ρ ω : ℝ) ∧
      (Y (Real.toNNReal t) ω ∈ Ioo a b →
        ContinuousAt (deriv w) (Y (Real.toNNReal t) ω)) := by sorry
