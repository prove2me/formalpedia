-- Prove2me | Theorems.Thm_ConnesGreen_canonical_fixed_cutoff_all_regularizations_iff_omitted_columns_zero
-- name    : ConnesGreen.canonical_fixed_cutoff_all_regularizations_iff_omitted_columns_zero
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:45:49.108125+00:00
-- url     : https://prove2.me/theorems/c825ce06-f1ce-4610-b4d4-a5bfe74bd984
-- title:
--   Fixed original cutoff works at every relative scale exactly when every omitted negative column vanishes
-- statement:
--   For an original positive window, unchanged finite actual-zero cutoff $F$, and $\alpha\ge0$, $$[\forall\varepsilon>0,\ \|B_FB_F^*\|\le\alpha\varepsilon]\iff[\forall\rho\notin F,\ b_\rho=0].$$ Here $B_F$ is the complete original complementary-negative synthesis and $b_\rho$ is its actual reflected pair column with analytic multiplicity. The accepted covariance-scale theorem gives $B_F=0$, and original basis custody and uniqueness give the column equivalence. This is a fixed-cutoff obstruction; accuracy-dependent cutoffs remain permitted. It does not supply the endpoint relative inverse-cost estimate.
-- source:
--   monocap-tech/weil, original native companion and RG0DependencyIntegration.lean. Source/proof cuts and declarations are extracted with the Lean elaborator. Original carrier, actual zeros, multiplicities and reflected /2 custody retained.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Theorems.Thm_WeilDefect_MarkerStability_covariance_relative_bound_all_regularizations_iff_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
/-- A single fixed ORIGINAL cutoff satisfying relative tail bounds at ALL
positive regularizations would have zero ORIGINAL background synthesis. -/
private theorem canonical_fixed_cutoff_all_regularizations_iff_background_zero
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖canonicalTailCovariance t ht F‖ ≤ α * ε) ↔
      canonicalBackgroundSynthesis t ht F = 0 := by
  exact covariance_relative_bound_all_regularizations_iff_zero
    (canonicalBackgroundSynthesis t ht F) α hα
end ConnesGreen

/-- Exact original-actor boundary: a fixed cutoff working at EVERY scale
requires ALL omitted original negative columns to vanish, not just be small. -/
theorem ConnesGreen.canonical_fixed_cutoff_all_regularizations_iff_omitted_columns_zero
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖canonicalTailCovariance t ht F‖ ≤ α * ε) ↔
      ∀ ρ : {ρ : CriticalZeros // ρ ∉ F},
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1 = 0 := by sorry
