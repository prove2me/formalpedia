-- Prove2me | Theorems.Thm_EdenVerified_s10_radial_and_singular_values
-- name    : EdenVerified.s10_radial_and_singular_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:24:15.958604+00:00
-- url     : https://prove2.me/theorems/cd68e13a-0542-5d0d-b202-708fd342ac5f
-- title:
--   Eden Verified: s10 radial and singular values
-- statement:
--   Radial trajectories and ambient singular values are independent of frequency.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L331-L343
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L331-L343

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s10_radial_and_singular_values (c ν : ℝ) (t : ℝ) (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₁ p) ∧
    radiusSq₂ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₂ p) ∧
    frequencyEvolution c ν t p 4 = Real.exp (-c*t)*p 4 ∧
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues ∧
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) ∧
    Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) := by sorry
