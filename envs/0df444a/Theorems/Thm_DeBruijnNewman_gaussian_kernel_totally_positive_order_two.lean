-- Prove2me | Theorems.Thm_DeBruijnNewman_gaussian_kernel_totally_positive_order_two
-- name    : DeBruijnNewman.gaussian_kernel_totally_positive_order_two
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T18:04:10.032297+00:00
-- url     : https://prove2.me/theorems/178ff04c-b784-48fe-a228-3e99590af15c
-- title:
--   The Gaussian kernel is totally positive of order 2
-- statement:
--   Total positivity of order 2 for the Gaussian kernel (Schoenberg 1947, the basic TP example): for a > 0, every 2×2 minor of (x,y) ↦ exp(−a(x−y)²) on strictly increasing nodes is nonnegative. Proof: a direct computation — the determinant equals e^{−a((x1−y1)²+(x2−y2)²)} − e^{−a((x1−y2)²+(x2−y1)²)}, and the exponent difference is 2a(x2−x1)(y2−y1) ≥ 0, so the first term dominates. Black-box role: the finite, fully explicit seed of the PF theory — the Gaussian is the prototypical Pólya frequency function (its full TP property is Schoenberg's basic composition formula), and this order-2 case is the concrete computation every higher-order argument bottoms out in.
-- source:
--   Decomposition of DeBruijnNewman.schoenberg_polya_fourier_real_zeros (626a294b-1b0a-43b9-aebe-aef9f7c9a57a), Prove2Me The de Bruijn-Newman Constant is Non-negative mission

import Mathlib

namespace DeBruijnNewman

theorem gaussian_kernel_totally_positive_order_two
    (a : ℝ) (ha : 0 < a) (x1 x2 y1 y2 : ℝ)
    (hx : x1 < x2) (hy : y1 < y2) :
    0 ≤ (Matrix.of ![![Real.exp (-a * (x1 - y1) ^ 2), Real.exp (-a * (x1 - y2) ^ 2)],
          ![Real.exp (-a * (x2 - y1) ^ 2), Real.exp (-a * (x2 - y2) ^ 2)]]).det := by
  sorry

end DeBruijnNewman
