-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
-- name    : AvramDividend.Classical.avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:01:23.341407+00:00
-- url     : https://prove2.me/theorems/beb033e4-7181-4aca-9f78-b1418f76c51d
-- title:
--   True original stopped Gaussian mesh noise is bounded by compensated source tube width on every left-mask prefix
-- statement:
--   For the original spectrally negative Lévy process with monotone physical-grid times, a left-start stopping mask selecting an arbitrary initial prefix k≤m+1 gives a compensated Gaussian source sum with absolute value ≤ε whenever the original compensated source coordinates through that prefix stay within ε. This is the genuine stopped-grid adaptation of the Abel sup-bound, including k=0, needed for the original finite-cap Gaussian limit and fixed-j positive-strip counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (m k : ℕ) (hk : k ≤ m + 1)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (hX0 : X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hTube : ∀ i ≤ k,
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      if i < k then Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ ε := by sorry
