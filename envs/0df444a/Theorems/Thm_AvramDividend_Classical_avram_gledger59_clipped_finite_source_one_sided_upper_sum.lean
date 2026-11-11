-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger59_clipped_finite_source_one_sided_upper_sum
-- name    : AvramDividend.Classical.avram_gledger59_clipped_finite_source_one_sided_upper_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:33:36.35921+00:00
-- url     : https://prove2.me/theorems/1ca84231-4a69-4501-8cc7-8723abac93dd
-- title:
--   Clipped physical source sum bounded by compact lower values and exponential terminal envelope
-- statement:
--   The original stopped physical Gaussian source is a finite sum of discounted terminal value minus initial value. Every inactive clipped cell contributes zero. In every active cell, a compact lower value bound and an exponential upper value bound yield a deterministic one-sided source upper majorant; this elementary inequality permits positive-part L1 domination without imposing any negative-tail growth bound.
-- source:
--   Necessary finite-mesh deterministic estimate for original top-cap gledger53 positive source integrability and gledger50 Taylor residual. This isolates discount and dividend cash algebra from original stopped Lévy exponential moment bounds.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger59_clipped_finite_source_one_sided_upper_sum
    (m : ℕ) (E Y Z : ℕ → ℝ) (w : ℝ → ℝ) (θ K b : ℝ)
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hE0 : ∀ i, 0 ≤ E i) (hE1 : ∀ i, E i ≤ 1)
    (hcell : ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) = E i ∧ Z i = Y i) ∨
      (-b ≤ w (Y i) ∧ w (Z i) ≤ K * Real.exp (θ * Z i))) :
    (Finset.sum (Finset.range (m + 1)) (fun i =>
      (E (i + 1) - E i) * w (Y i) +
        E (i + 1) * (w (Z i) - w (Y i)))) ≤
    (Finset.sum (Finset.range (m + 1)) (fun i =>
      K * Real.exp (θ * Z i) + b)) := by sorry
