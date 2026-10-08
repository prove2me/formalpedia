-- Prove2me | Theorems.Thm_ConnesGreen_canonical_background_bound
-- name    : ConnesGreen.canonical_background_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:30:01.449439+00:00
-- url     : https://prove2.me/theorems/a831cad3-ade6-4e29-ac0e-65e2292e16ff
-- title:
--   Original complete physical background is bounded by the complementary Mellin coefficient energy
-- statement:
--   For every original supported test $g$ on $t>0$ and every reflection-closed ORIGINAL finite actual-zero packet $S$, we prove
--   $$\|B_{t,S}^*\mathrm{sourceEmbed}_t(\mathrm{problemOneL}(g))\|^2\le
--   \sum_{\rho\notin S} m_\rho\,|\widehat g(\rho)|^2.$$
--   The displayed sum ranges over the entire original actual-zero complement. Original source/Mellin pairing identifies each raw weighted analysis norm square with its own analytic multiplicity times the Mellin coefficient norm square. The original pair columns use division by two, so the parallelogram identity makes their combined energy half the two raw energies. Summability of original actor columns and Cauchy-Schwarz first give convergence of their analysis sums, and domination by their combined energy gives convergence of the raw coefficient sum. Reflection closure makes complement membership invariant under the ORIGINAL involutive zero reflection. Reindexing its genuine convergent sum therefore identifies combined complementary actor energy with the complete complementary coefficient energy. The negative component is bounded by that nonnegative combined energy. Finally the exact original background synthesis adjoint norm is its complementary analysis sum. The public statement unfolds only the native coefficientEnergy definition; no zero configuration, multiplicity or Hilbert carrier is replaced.
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

theorem ConnesGreen.canonical_background_bound (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hS : ∀ ρ ∈ S, reflectedZero ρ ∈ S) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
      ∑' ρ : CriticalZeros, if ρ ∈ S then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2 := by sorry
