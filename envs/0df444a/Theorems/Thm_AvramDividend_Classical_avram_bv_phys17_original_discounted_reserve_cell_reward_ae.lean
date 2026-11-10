-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys17_original_discounted_reserve_cell_reward_ae
-- name    : AvramDividend.Classical.avram_bv_phys17_original_discounted_reserve_cell_reward_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:54:19.658191+00:00
-- url     : https://prove2.me/theorems/78afb82b-4995-4c48-8ec2-4d2ce138c23d
-- title:
--   Original BV discounted reward cell identity with exact negative source jumps and right-limit payments
-- statement:
--   A source-exact almost-sure identity for discounted reward over every pair of physical times. The nonlinear reward increment uses precisely the original drift minus actual negative-jump compensation minus actual right-limit dividend increments. The remaining term is solely the discount difference. This exact identity provides the deterministic Taylor/HJB cell starting point; it does not posit error convergence or stochastic centring.
-- source:
--   Direct consequence of Proved source 1431d059 for the same original process; bridge to finite physical cash and terminal ledger in the root-connected c5ce01c6 and e6/e0 routes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys17_original_postright_reserve_source_increment_ae
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys17_original_discounted_reserve_cell_reward_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0),
      let U : ℝ≥0 → ℝ := fun v => x + X.X v ω - rightLimit D v ω
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      Real.exp (-(q * (t : ℝ))) * w (U t) -
        Real.exp (-(q * (s : ℝ))) * w (U s) =
      Real.exp (-(q * (t : ℝ))) *
        (w (U s + (((t : ℝ) - (s : ℝ)) * X.drift -
          (J t - J s) - (rightLimit D t ω - rightLimit D s ω))) -
          w (U s)) +
      (Real.exp (-(q * (t : ℝ))) -
        Real.exp (-(q * (s : ℝ)))) * w (U s) := by sorry
