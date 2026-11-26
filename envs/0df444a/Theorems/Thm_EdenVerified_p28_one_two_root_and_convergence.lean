-- Prove2me | Theorems.Thm_EdenVerified_p28_one_two_root_and_convergence
-- name    : EdenVerified.p28_one_two_root_and_convergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:56.03104+00:00
-- url     : https://prove2.me/theorems/6b830e5a-af54-4a54-83a8-9e2c843c26c9
-- title:
--   Eden Verified: p28 one two root and convergence
-- statement:
--   Strict positivity and negativity around the limiting root seven halves.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1303-L1327
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1303-L1327

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p28_one_two_root_and_convergence (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 1)) :
    (∀ d : ℝ, d ∈ Ioo 0 (7/2) → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) (7/2) = 0 ∧
    (∀ d : ℝ, d ∈ Ioc (7/2) 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 (7/2)) := by sorry
