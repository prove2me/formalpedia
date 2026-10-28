-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
-- name    : AvramDividend.Classical.bv_esscher_positive_tail_real_total_mass_of_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:08:35.117223+00:00
-- url     : https://prove2.me/theorems/6f5b9542-0126-4b35-a773-15f34c2c3025
-- title:
--   Exact real total mass of the BV root-discounted Esscher strict jump-tail
-- statement:
--   For a bounded-variation spectrally negative Lévy process and positive Esscher root solving ψφ=q, the real positive-time integral of the discounted positive jump-magnitude strict tail equals the real discounted jump first moment exactly. It composes the Proved generic real layer-cake formula with the Proved BV root subcritical moment and exact Esscher tail measure identity. This supplies the exact integral κ=ρ normalisation after division by the positive BV drift for the cstar-connected Open scaled renewal identification.
-- source:
--   Proved generic positive_jump_tail_real_integral_eq_firstMoment_toReal, bv_esscher_root_subcritical_kernel_mass, and esscher_tail_kernel_mass_as_discounted_first_moment.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_eq_firstMoment_toReal
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_positive_tail_real_total_mass_of_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    (∫ t in Ioi (0 : ℝ),
      ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) =
      ∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by sorry
