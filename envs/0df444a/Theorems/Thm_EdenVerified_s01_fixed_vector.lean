-- Prove2me | Theorems.Thm_EdenVerified_s01_fixed_vector
-- name    : EdenVerified.s01_fixed_vector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:21:30.321684+00:00
-- url     : https://prove2.me/theorems/3282ba78-d452-44fa-a57a-c60c2c21c8c1
-- title:
--   Eden Verified: s01 fixed vector
-- statement:
--   Ordinary limits for every fixed nonzero exterior vector.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L130-L136
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L130-L136

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s01_fixed_vector (c : ℝ) (p : PhaseSpace) (k : ℕ)
    (v : ExteriorSpace k) (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) ∧
    limsup (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v := by sorry
