-- Prove2me | Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
-- name    : ConnesGreen.canonical_signed_actor_arithmetic
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:54:10.827599+00:00
-- url     : https://prove2.me/theorems/920077f7-7487-4591-be78-dc4c0825f0e3
-- title:
--   Full original signed actor arithmetic identity on the completed carrier
-- statement:
--   For every positive window and original supported test, the squared norm of the complete positive actor analysis minus the squared norm of the complete negative actor analysis equals the real part of the full original Weil distribution on its convolution square. The sum runs over actual zeta zeros with analytic multiplicities; original reflected pair columns retain their factor one half. Both norm-square series genuinely converge. No positivity or RH premise is used.
-- source:
--   monocap-tech/weil at 28829dbeeee2ba23d6c0f3cedaf22952174099c2; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_signed_actor_arithmetic (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) :
    ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
      ‖(canonicalNegativeSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
        (weilDistribution (conv g (starInv g))).re := by sorry
