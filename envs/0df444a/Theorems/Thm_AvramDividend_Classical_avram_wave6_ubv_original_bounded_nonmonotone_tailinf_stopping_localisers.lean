-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:56:19.427361+00:00
-- url     : https://prove2.me/theorems/ad6494d6-accc-4c34-a782-41b089064c1f
-- title:
--   Original UBV genuinely bounded stopping localisers from arbitrary nonmonotone clocks
-- statement:
--   For the original source SpectrallyNegativeLevy P 𝓕 and actual admissible strategy D, take genuine source right-continuous stopping times S_n, not assumed monotone, with liminf S_n=∞ P-a.s. Define the localiser at n by clipping the ruin-clipped tail-infimum of later S clocks at the deterministic integer horizon n. Prove this is a genuine source stopping time, is at most n on every path, is increasing, and converges to actual ruinTime almost surely including ruin zero and infinity. The diagonal ENNReal clipping identity preserves the supremum. No extra smoothness, variation, boundary, atomlessness or filtration hypothesis; no stopped martingale budget is assumed or proved.
-- source:
--   Proved original tail-inf stopping lemma dae08fbd-1984-4610-8a6c-4d6acc3e1a75, ruin liminf b6f6314c-f08c-4ac7-987f-77eeccb7e5fd, newly authored diagonal supremum helper avram_wave6_monotone_ennreal_diagonal_nat_clip_sup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq
import Theorems.Thm_avram_wave6_monotone_ennreal_diagonal_nat_clip_sup

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞))) ∧
    (∀ n ω, min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞) ≤
      (n : ℝ≥0∞)) ∧
    (∀ ω, Monotone
      (fun n : ℕ => min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞))) ∧
    (∀ᵐ ω ∂P,
      (⨆ n : ℕ, min (⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) (n : ℝ≥0∞)) =
      ruinTime X x D ω) := by sorry
