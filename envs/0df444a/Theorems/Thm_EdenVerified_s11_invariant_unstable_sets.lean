-- Prove2me | Theorems.Thm_EdenVerified_s11_invariant_unstable_sets
-- name    : EdenVerified.s11_invariant_unstable_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:24:58.714413+00:00
-- url     : https://prove2.me/theorems/8667d684-902a-57ea-af02-2a233b7d6797
-- title:
--   Eden Verified: s11 invariant unstable sets
-- statement:
--   Strict invariance and nonlinear epsilon-delta instability, already within A.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L422-L429
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L422-L429

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s11_invariant_unstable_sets (c : ℝ) (K : Set PhaseSpace)
    (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor, Metric.infDist p K < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) K) := by sorry
