-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_signed_gaussian_positive_l1
-- name    : AvramDividend.Classical.avram_wave3_05_signed_gaussian_positive_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:49:47.105561+00:00
-- url     : https://prove2.me/theorems/4a550821-abb2-4c6e-a46d-b29e902b836e
-- title:
--   Original Gaussian Neumann signed density is L1 from positive-reserve quadratic-geometric domination
-- statement:
--   For the signed Gaussian Volterra Neumann powers P_n and their positive envelope F_n, assume only the source-available bounds on positive reserves: L1 of the individual powers, F_n≥0 and |P_n|≤F_n for x>0, quadratic-geometric pointwise decay there, and summable total masses. Then the signed infinite density sum is integrable over (0,∞). The proof supports the envelope by zero away from positive reserves, derives pointwise summability from the Proved renewal bound and applies nonnegative Tonelli plus signed norm domination. This avoids imposing false global positivity on the untruncated native Gaussian kernel.
-- source:
--   Avram-Palmowski-Pistorius (2007), Gaussian generator Lemma 4; Proved renewal_density_series_summable_of_geometric_power_bound 617e5955, nonnegative_integrable_tsum_of_summable_integrals 2df366d2, and Gaussian envelope constructor 0802e5ff.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_signed_gaussian_positive_l1
    (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ F n x)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 < x → |P n x| ≤ F n x)
    (hFbound : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hFmass : Summable (fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), F n x ∂volume)) :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, P n x)
      (Ioi (0 : ℝ)) volume := by sorry
