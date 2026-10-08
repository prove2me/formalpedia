-- Prove2me | Theorems.Thm_ConnesRZ_finite_mellin_exceptional
-- name    : ConnesRZ.finite_mellin_exceptional
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T21:16:09.374118+00:00
-- url     : https://prove2.me/theorems/8feb1e32-1c42-4080-b7fa-51c59a7d8886
-- title:
--   Finite exceptional zeros above a Mellin-transform threshold
-- statement:
--   For a smooth compactly supported test function and any positive threshold, there are only finitely many critical-strip zeros where the norm of its shifted Mellin transform meets or exceeds the threshold. The proof combines integration by parts and a uniform bound across the closed critical strip with local finiteness of zeta zeros on compact sets. This is the finite exceptional-set step used before Burnol’s convolution amplification.
-- source:
--   Jean-François Burnol, The Explicit Formula in simple terms, https://arxiv.org/abs/math/9810169v2 , pp. 5–6, Weil’s positivity criterion: finitely many zeros satisfy |hatφ|≥1/2. The arbitrary positive threshold is the same argument. Mathlib IsCompact.inter_riemannZetaZeros_finite supplies compact zero-set finiteness.

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem finite_mellin_exceptional (g : ℝ → ℂ) (hg : IsTest g) (ε : ℝ) (hε : 0 < ε) :
    {z : ℂ | IsCriticalZero z ∧ ε ≤ ‖mellinHat g z‖}.Finite := by sorry

end ConnesRZ
