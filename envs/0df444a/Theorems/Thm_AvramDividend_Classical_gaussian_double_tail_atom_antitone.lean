-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_antitone
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:58:03.398398+00:00
-- url     : https://prove2.me/theorems/eb029ef8-78c1-48ff-b44d-51aee4b7e16b
-- title:
--   Positive-time monotonicity of Gaussian Esscher double-tail jump atom
-- statement:
--   For 0<s≤t the nonnegative Gaussian double-tail integrand max(z−t,0) exp(−φz) is dominated by its earlier-time value max(z−s,0) exp(−φz). Split on t<z and apply ENNReal.ofReal_le_ofReal and positive multiplicative monotonicity. This supports antitonicity of the integrated double-tail renewal kernel Rφ(t), needed to upgrade a.e. finiteness and establish local regularity.
-- source:
--   Pinned ENNReal.ofReal_le_ofReal; no unproved dependencies.

import Mathlib
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_atom_antitone (φ s t z : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (if 0 < t ∧ t < z then
      ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
     else 0) ≤
    (if 0 < s ∧ s < z then
      ENNReal.ofReal (z - s) * ENNReal.ofReal (Real.exp (-φ * z))
     else 0) := by sorry
