-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_total_covariance_le_of_original_quadratic_shift
-- name    : ConnesGreen.RG0Integration.total_covariance_le_of_original_quadratic_shift
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:39:25.673544+00:00
-- url     : https://prove2.me/theorems/d13ddd3a-82ea-49f6-817f-0d8320d840a4
-- title:
--   Complete original actual-zero covariance domination from a stated physical quadratic shift
-- statement:
--   On the original completed physical carrier, let $P$ and $N$ be the original full positive and full negative Green syntheses. If $\|P^*x\|^2-\|N^*x\|^2\ge-k\|x\|^2$ for every physical vector and $k\le\varepsilon$, then $$NN^*\le PP^*+\varepsilon I.$$ Both actors are constructed from RG-0 with their actual-zero columns, analytic multiplicities and reflected pair normalization. The quadratic shift is an explicit premise. The theorem does not establish the native arithmetic value of that shift or unshifted positivity.
-- source:
--   monocap-tech/weil: WeilDefect/Connes/RG0DependencyIntegration.lean, original actor and metric adapters at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5; proof and statement boundaries recovered with Lean elaborator metadata.

import Theorems.Thm_WeilDefect_MarkerStability_covariance_le_regularized_of_quadratic_shift
import Definitions.Def_ConnesGreen_RG0_original_actors
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.total_covariance_le_of_original_quadratic_shift (t : ℝ) (ht : 0 < t)
    (k ε : ℝ) (hkε : k ≤ ε)
    (hbound : ∀ x : Physical t, -k * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalNegativeSynthesis t ht).adjoint x‖ ^ 2) :
    canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint ≤
      canonicalPositiveCovariance t ht + ε • 1 := by sorry
