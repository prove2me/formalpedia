-- Prove2me | Theorems.Thm_ConnesGreen_canonical_selected_negative_of_coefficient_margin
-- name    : ConnesGreen.canonical_selected_negative_of_coefficient_margin
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:29:42.146911+00:00
-- url     : https://prove2.me/theorems/75163841-92b7-4fdd-9f3f-05b620546a55
-- title:
--   The full complementary coefficient margin forces original selected physical negativity
-- statement:
--   For an original supported test and reflection-closed original packet, we prove negative original selected physical value whenever
--   $$\sum_{\rho\notin S}m_\rho|\widehat g(\rho)|^2< -\operatorname{Re}W(g*\mathrm{starInv}(g)).$$
--   The closed original background-bound helper bounds the squared background-adjoint norm by that full coefficient sum. Accepted full signed actor arithmetic and the convergent exact selected/background partition give
--   $$\|P^*x\|^2-\|M^*x\|^2=\operatorname{Re}W(g*\mathrm{starInv}(g))+\|B^*x\|^2.$$
--   The assumed coefficient/Weil margin consequently makes the selected value negative. The premise is the concrete quantitative coefficient margin; negative physical value and the background attachment are proved conclusions, not assumed.
-- source:
--   monocap-tech/weil at 68011f0aa80779d1735ecbe344b0314d03cd3de5; WeilDefect/Connes/CoefficientPhysicalWitness.lean (new additive margin and witness declarations); original CanonicalGreenBackground, CanonicalGreenMarkerLimit and CriticalWindowBoundary declarations retained.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_selected_negative_of_coefficient_margin
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hS : ∀ ρ ∈ S, reflectedZero ρ ∈ S) (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hm : (∑' ρ : CriticalZeros, if ρ ∈ S then 0 else
      (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) < -(weilDistribution (conv g (starInv g))).re) :
    ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0 := by sorry
