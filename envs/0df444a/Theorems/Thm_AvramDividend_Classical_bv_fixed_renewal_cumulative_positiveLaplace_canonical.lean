-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_fixed_renewal_cumulative_positiveLaplace_canonical
-- name    : AvramDividend.Classical.bv_fixed_renewal_cumulative_positiveLaplace_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:28:57.166992+00:00
-- url     : https://prove2.me/theorems/cad1f045-cf66-47b7-aaa6-c4ec80ef1dc2
-- title:
--   A fixed BV renewal measure has the canonical-tilt cumulative positive Laplace formula on a whole half-line
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process and q>0, construct one positive geometric renewal measure β, with finite lower cumulative masses and a positive atom at zero, whose cumulative positive Laplace transform has the explicit geometric formula for every sufficiently large discount. The Esscher shift is written canonically as q/X.drift in the theorem statement, so later results can combine the transform with the BV Lévy-exponent identity without reconciling hidden existential tilt witnesses.
-- source:
--   Proved supported BV kernel and geometric renewal/Laplace package; canonical tilt q/drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_fixed_renewal_cumulative_positiveLaplace_canonical
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (β : Measure ℝ) (b : ℝ),
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ≥0, ENNReal.ofReal
                ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
                ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))⁻¹) := by sorry
