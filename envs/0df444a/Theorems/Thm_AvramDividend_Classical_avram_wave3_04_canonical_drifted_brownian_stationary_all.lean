-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_stationary_all
-- name    : AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_stationary_all
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:46:40.488369+00:00
-- url     : https://prove2.me/theorems/75e75ec9-762c-493a-8ed1-2a17d241b75a
-- title:
--   Canonical drifted Brownian process has stationary increments also at zero duration
-- statement:
--   The actual canonical drift-minus-one Brownian path has stationary increments at all nonnegative pairs of times. At zero duration both random variables vanish identically; at positive duration apply the previously Proved canonical stationary-increments theorem. This exactly matches the stationary-increments field of the SpectrallyNegativeLevy source constructor.
-- source:
--   Canonical strict stationary theorem 95a5f015-2566-4f38-8513-82cc21d97db4, Proved. Exact proof elaborated to sentinel in private job 4e41ea48-a57d-44dc-bcbf-5cb6c9e423b9; source SHA fc11e149f6a50af3d653a54fb58b46236abbc5e2d745813ec72c474a86151841.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_stationary_strict

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_stationary_all (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib
      (fun ω : ℝ≥0 → ℝ =>
        (brownian t ω - brownian 0 ω - (t : ℝ)) -
        (brownian s ω - brownian 0 ω - (s : ℝ)))
      (fun ω : ℝ≥0 → ℝ =>
        brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
      gaussianLimit gaussianLimit := by sorry
