-- Prove2me | Theorems.Thm_ConnesGreen_canonical_supported_neutral_weil_nonnegative_iff_complementary_columns_zero
-- name    : ConnesGreen.canonical_supported_neutral_weil_nonnegative_iff_complementary_columns_zero
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T13:46:04.679309+00:00
-- url     : https://prove2.me/theorems/8d52707a-7ab6-4015-8182-a2caa390c45c
-- title:
--   Neutral-test Weil nonnegativity is exactly orthogonality to every actual complementary negative column
-- statement:
--   For the SAME original supported neutral test and unchanged finite actual-zero packet $S$, we prove
--   $$0\le\operatorname{Re}W(g*\operatorname{starInv}(g))\quad\Longleftrightarrow\quad
--   \forall\rho\in\operatorname{CriticalZeros}\setminus S,\
--   \langle v^-_{t,\rho},\operatorname{sourceEmbed}_t(\operatorname{problemOneL}(g))\rangle=0.$$
--   The closed original neutral arithmetic balance and norm-zero argument first identify local Weil nonnegativity with annihilation of the COMPLETE background adjoint. The exact original column-synthesis adjoint-coordinate identity then identifies each background coordinate with the inner product against its ACTUAL complementary negative column. Adjoint zero implies every coordinate zero; conversely pointwise vanishing of ALL coordinates implies the l2 vector is zero by extensionality. No finite complement truncation, zero enumeration substitution, unsigned coefficient replacement or multiplicity normalization change is made. This certifies an exact local arithmetic obstruction on the original test vector, without asserting its orthogonality or its Weil sign unconditionally.
-- source:
--   monocap-tech/weil parent 44f7e38ec554b54547a64cf3c464b9986101a4fb; original neutral arithmetic balance and additive NeutralArithmeticObstruction.lean equivalences

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_supported_neutral_weil_nonnegative_iff_complementary_columns_zero (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 = 0) :
    0 ≤ (weilDistribution (conv g (starInv g))).re ↔
    ∀ ρ : {ρ : CriticalZeros // ρ ∉ S},
      ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1,
        sourceEmbed t (problemOneL g)⟫_ℂ = 0 := by sorry
