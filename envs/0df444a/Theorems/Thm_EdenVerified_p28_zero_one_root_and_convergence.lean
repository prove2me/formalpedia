-- Prove2me | Theorems.Thm_EdenVerified_p28_zero_one_root_and_convergence
-- name    : EdenVerified.p28_zero_one_root_and_convergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:42.104109+00:00
-- url     : https://prove2.me/theorems/5fbd2c3c-0bfe-5d24-b40e-bfae0c732d19
-- title:
--   Eden Verified: p28 zero one root and convergence
-- statement:
--   Strict positivity and negativity around the limiting root three, in either plane
--   order.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1276-L1300
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1276-L1300

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p28_zero_one_root_and_convergence (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 1) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    (∀ d : ℝ, d ∈ Ioo 0 3 → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) 3 = 0 ∧
    (∀ d : ℝ, d ∈ Ioc 3 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 3) := by sorry
