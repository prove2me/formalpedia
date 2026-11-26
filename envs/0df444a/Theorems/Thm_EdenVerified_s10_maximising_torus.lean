-- Prove2me | Theorems.Thm_EdenVerified_s10_maximising_torus
-- name    : EdenVerified.s10_maximising_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:25:19.699584+00:00
-- url     : https://prove2.me/theorems/26a31046-1d5a-45c9-aa97-ad99dfc8d768
-- title:
--   Eden Verified: s10 maximising torus
-- statement:
--   Both complete maximising sets remain precisely T, for every frequency.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L373-L387
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L373-L387

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s10_maximising_torus (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' attractor) (4+4/c) ∧
      ∀ p ∈ attractor, frequencyFiniteTimeDimension c ν t p = 4+4/c ↔ p ∈ torus) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' attractor) (4+4/c) ∧
    (∀ p ∈ attractor, frequencyAsymptoticDimension c ν p = 4+4/c ↔ p ∈ torus) ∧
    frequencyGlobalLyapunovDimension c ν attractor = 4+4/c ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p))) := by sorry
