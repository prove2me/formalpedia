-- Prove2me | Theorems.Thm_EdenVerified_D10_finite_time_convention
-- name    : EdenVerified.D10_finite_time_convention
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:27:24.119669+00:00
-- url     : https://prove2.me/theorems/91eb7ab1-1541-44c9-ace3-ce468eea3e4b
-- title:
--   Eden Verified: D10 finite time convention
-- statement:
--   The finite-time admissible set agrees with the Kaplan--Yorke convention applied
--   to the normalized logarithmic spectrum.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L654-L661
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L654-L661

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D10_finite_time_convention (c : ℝ) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) ∧
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) := by sorry
