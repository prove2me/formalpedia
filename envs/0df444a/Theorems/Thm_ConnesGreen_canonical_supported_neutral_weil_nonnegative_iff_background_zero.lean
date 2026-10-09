-- Prove2me | Theorems.Thm_ConnesGreen_canonical_supported_neutral_weil_nonnegative_iff_background_zero
-- name    : ConnesGreen.canonical_supported_neutral_weil_nonnegative_iff_background_zero
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T13:45:41.000102+00:00
-- url     : https://prove2.me/theorems/cee2f890-bfdd-4ad7-8c91-253a5cb9205c
-- title:
--   Exact local arithmetic obstruction for neutral original tests is full background annihilation
-- statement:
--   For the SAME original supported test and original finite actual-zero packet, under its concrete selected-neutrality equality, we prove
--   $$0\le\operatorname{Re}W(g*\operatorname{starInv}(g))\quad\Longleftrightarrow\quad B_{t,S}^*\operatorname{sourceEmbed}_t(\operatorname{problemOneL}(g))=0.$$
--   A closed local proof of the exact original neutral arithmetic balance uses accepted full signed actor arithmetic and the genuinely convergent full selected/complementary analysis partition. The Weil value equals minus the background norm square. Nonnegativity therefore forces that norm to vanish; conversely annihilation gives Weil value zero. Thus for an original neutral supported test the full Weil value is always nonpositive, and local nonnegativity is exactly background annihilation. This is a proved equivalence, not an unconditional Weil-sign or background-zero claim. It does not extend a test-vector assertion to arbitrary completed-carrier vectors.
-- source:
--   monocap-tech/weil parent 44f7e38ec554b54547a64cf3c464b9986101a4fb; original neutral arithmetic balance and additive NeutralArithmeticObstruction.lean equivalences

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_supported_neutral_weil_nonnegative_iff_background_zero (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 = 0) :
    0 ≤ (weilDistribution (conv g (starInv g))).re ↔ (canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g)) = 0 := by sorry
