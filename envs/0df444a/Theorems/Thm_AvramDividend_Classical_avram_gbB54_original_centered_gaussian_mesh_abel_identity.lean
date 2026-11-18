-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54_original_centered_gaussian_mesh_abel_identity
-- name    : AvramDividend.Classical.avram_gbB54_original_centered_gaussian_mesh_abel_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:37:47.957994+00:00
-- url     : https://prove2.me/theorems/1019c8c8-5cac-4119-b0e2-75ad9727de21
-- title:
--   Original Lévy physical centred Gaussian mesh has exact discounted Abel terminal-and-drift representation
-- statement:
--   For any original spectrally negative Lévy source and arbitrary physical grid s_i, the discounted centred increment source with Z_i=X(s_{i+1})-X(s_i)-(s_{i+1}-s_i)c has an exact finite pathwise summation-by-parts formula in terms of centred source coordinates X(s_i)-s_i c. This permits a route to the Gaussian source L1 limit through deterministic Riemann integration on the narrow upper-strip tube.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54_original_centered_gaussian_mesh_abel_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (ω : Ω) (m : ℕ) (s : ℕ → ℝ≥0) :
    let a : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    let b : ℕ → ℝ := fun i => X.X (s i) ω - (s i : ℝ) * X.c
    (Finset.range (m + 1)).sum (fun i =>
      a i * (X.X (s (i + 1)) ω - X.X (s i) ω -
        ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)) =
    a m * b (m + 1) - a 0 * b 0 +
      (Finset.range m).sum (fun i =>
        (a i - a (i + 1)) * b (i + 1)) := by sorry
