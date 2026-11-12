-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise22_original_gaussian_cutoff_martingale_l1
-- name    : AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_martingale_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T09:06:22.644813+00:00
-- url     : https://prove2.me/theorems/45cf62b8-ecf0-4be9-89bc-928240565d03
-- title:
--   Finite-cutoff intrinsic Gaussian residual is an original-filtration martingale
-- statement:
--   At every fixed cutoff n, the original intrinsic residual X-c t minus actual compensated small negative band and actual uncompensated large jumps is integrable at all times and has the conditional martingale identity with respect to the original right-continuous filtration. No auxiliary Brownian process on the original space is assumed.
-- source:
--   The last missing source identification for 08823aa3. Proved original cutoff adaptedness 42ada2ca, shifted future path independence ce77d378, signed marked annulus centring 6de0a6db, and original triplet. Fixed-cutoff identity to be proved before passing via quantitative L2 convergence 41b16fe8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_martingale_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ,
      (∀ t : ℝ≥0, Integrable
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P
            (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ω =
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) := by sorry
