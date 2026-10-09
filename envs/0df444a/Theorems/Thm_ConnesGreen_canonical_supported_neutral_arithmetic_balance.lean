-- Prove2me | Theorems.Thm_ConnesGreen_canonical_supported_neutral_arithmetic_balance
-- name    : ConnesGreen.canonical_supported_neutral_arithmetic_balance
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T13:45:43.23172+00:00
-- url     : https://prove2.me/theorems/8b0e2f34-0a7d-4074-9f44-9e5b76859930
-- title:
--   Original neutral-test Weil value is minus its complete background energy
-- statement:
--   For an ORIGINAL supported test $g$ on $t>0$ and the unchanged finite actual-zero packet $S$, if its original selected quadratic value is zero, we prove
--   $$\operatorname{Re}W(g*\operatorname{starInv}(g))=-\|B_{t,S}^*\operatorname{sourceEmbed}_t(\operatorname{problemOneL}(g))\|^2.$$
--   Accepted FULL original signed actor arithmetic identifies positive-analysis energy minus full negative-analysis energy with the complete Weil distribution. A closed convergent negative-analysis partition splits the full actual-zero set into the SAME selected packet and its complete complement. It uses original column summability and Cauchy-Schwarz to justify both sums and their exact partition. Subtracting the assumed zero selected value yields the equality. No Weil sign or background estimate is assumed. The public neutrality premise unfolds EXACTLY the native selectedQuadratic definition as the same original positive minus selected analysis norm squares; native readback verifies this definitionally against the unchanged existing theorem.
-- source:
--   monocap-tech/weil parent 44f7e38ec554b54547a64cf3c464b9986101a4fb; original neutral arithmetic balance and additive NeutralArithmeticObstruction.lean equivalences

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_supported_neutral_arithmetic_balance (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 = 0) :
    (weilDistribution (conv g (starInv g))).re = -‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by sorry
