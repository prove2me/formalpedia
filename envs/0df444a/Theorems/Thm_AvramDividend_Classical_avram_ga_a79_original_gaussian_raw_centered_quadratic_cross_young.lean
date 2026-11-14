-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a79_original_gaussian_raw_centered_quadratic_cross_young
-- name    : AvramDividend.Classical.avram_ga_a79_original_gaussian_raw_centered_quadratic_cross_young
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:45:27.60655+00:00
-- url     : https://prove2.me/theorems/43287515-b5b6-4025-bf00-3ab8249bdb24
-- title:
--   Original Gaussian raw-versus-drift-centred source quadratic difference has arbitrarily small Young energy bound
-- statement:
--   For any real drift-centred source increment z, actual raw shift d and epsilon positive, the absolute difference of raw and centred squares is bounded by epsilon times centred squared energy plus (1+1/epsilon) times deterministic squared drift.
-- source:
--   Direct original b0d9951c stopped Gaussian spatial compensated exact error ga_a77 and ga_a78: control raw-vs-centred drift quadratic cross.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a79_original_gaussian_raw_centered_quadratic_cross_young (z d ε : ℝ) (hε : 0 < ε) :
    |(z + d)^2 - z^2| ≤ ε * z^2 + (1 + 1 / ε) * d^2 := by sorry
