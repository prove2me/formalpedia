-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_generator_dividend_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_p4_f_assembly_generator_dividend_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:44:54.604132+00:00
-- url     : https://prove2.me/theorems/5739f720-8663-48a1-9212-67a4a2cc72d2
-- title:
--   Original Levy generator and right-dividend residuals have a jointly nonpositive finite-mesh sum
-- statement:
--   For the original spectrally negative Levy X and original dividend strategy D, the discounted finite-mesh HJB generator drift residual and true right-dividend payment secant residual have nonpositive sum at interior postpayment reserves. The previously verified two original-source mesh-sign lemmas are combined without introducing a surrogate process or compensation hypothesis. This is the signed G+H mesh interface only; a stochastic Ito cell identity, integral/martingale limits, and boundary analysis remain separate obligations.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i) and equations (5.11), (5.12); accepted source mesh sign theorems 220513b9-f200-41f6-ab0b-5540d68a8eb5 and 0b2dd7dd-1cef-463f-86e1-b2d0380c4723.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_generator_dividend_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (N : ℕ) (clock : Fin N → ℝ≥0) (δ : Fin N → ℝ) (ω : Ω)
    (hδ : ∀ i, 0 ≤ δ i)
    (hpos : ∀ i, 0 < x + X.X (clock i) ω - rightLimit D (clock i) ω)
    (hcap : ∀ i, ENNReal.ofReal (x + X.X (clock i) ω -
      rightLimit D (clock i) ω) < C)
    (hclock : ∀ i, clock i = 0 ∨
      (clock i : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i : Fin N,
      (δ i * Real.exp (-(q * (clock i : ℝ)))) *
        (X.generator w (x + X.X (clock i) ω - rightLimit D (clock i) ω) -
         q * w (x + X.X (clock i) ω - rightLimit D (clock i) ω))) +
    (∑ i : Fin N,
      Real.exp (-(q * (clock i : ℝ))) *
        ((rightLimit D (clock i) ω - D (clock i) ω) -
         (w (riskProcess X x D (clock i) ω) -
          w (riskProcess X x D (clock i) ω -
            (rightLimit D (clock i) ω - D (clock i) ω))))) ≤ 0 := by sorry
