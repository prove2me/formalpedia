-- Prove2me | Theorems.Thm_EdenVerified_D09_attainment_and_infimum
-- name    : EdenVerified.D09_attainment_and_infimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:27:04.167405+00:00
-- url     : https://prove2.me/theorems/d3d6cdaa-acbb-4dbf-880e-ddb392a39597
-- title:
--   Eden Verified: D09 attainment and infimum
-- statement:
--   The finite-time maximum is attained, and the global definition keeps the infimum
--   over positive real times outside the spatial supremum.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L608-L621
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L608-L621

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D09_attainment_and_infimum (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) (K : Set PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d}.Nonempty ∧
    IsCompact {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d}
      (finiteTimeDimension c t p) ∧
    globalLyapunovDimension c K =
      sInf {v : ℝ | ∃ τ : ℝ, 0 < τ ∧ v = sSup (finiteTimeDimension c τ '' K)} := by sorry
