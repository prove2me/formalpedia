-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
-- name    : AvramDividend.Classical.avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:03:33.174337+00:00
-- url     : https://prove2.me/theorems/becdaa6c-97ce-4212-835c-082dcc9656ac
-- title:
--   Finite original BV stopped physical-mesh terminal reward ledger with source-exact compensated jumps
-- statement:
--   On one almost-sure source-exact event, the discounted reward at the final physical grid time minus its initial value equals the finite sum of true original drift, source negative-jump and right-limit dividend changes passed through w, plus exact discount changes. Uniform, stopped and pathwise clipped meshes are included without refinement assumptions. This is a terminal reward ledger, leaving the Stieltjes payment identity and C1/L1 error bounds to their own proved source lemmas.
-- source:
--   Derived by telescoping the accepted discounted reward cell identity 78afb82b using the identical original source jump series J and dividend right limits at all cells; designed for use with the six-term stopped physical cash ledger d51199a8 and parent c5ce01c6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys17_original_discounted_reserve_cell_reward_ae
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      let U : ℝ≥0 → ℝ := fun v => x + X.X v ω - rightLimit D v ω
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      Real.exp (-(q * (u n : ℝ))) * w (U (u n)) -
        Real.exp (-(q * (u 0 : ℝ))) * w (U (u 0)) =
      ∑ i ∈ Finset.range n,
        (Real.exp (-(q * (u (i + 1) : ℝ))) *
          (w (U (u i) +
            (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift -
              (J (u (i + 1)) - J (u i)) -
              (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) -
           w (U (u i))) +
         (Real.exp (-(q * (u (i + 1) : ℝ))) -
          Real.exp (-(q * (u i : ℝ)))) * w (U (u i))) := by sorry
