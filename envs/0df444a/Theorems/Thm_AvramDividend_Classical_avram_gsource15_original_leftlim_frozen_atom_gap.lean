-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gsource15_original_leftlim_frozen_atom_gap
-- name    : AvramDividend.Classical.avram_gsource15_original_leftlim_frozen_atom_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:41:59.352698+00:00
-- url     : https://prove2.me/theorems/effed959-d68e-4f12-9197-b335302644c4
-- title:
--   Original-process Gaussian frozen source prepayment gap equals dividend right atom
-- statement:
--   For any original spectrally negative Levy process and admissible dividend strategy, at a strictly positive time where the source X is continuous from the left, the predictable left-limit of the postpayment reserve equals its pointwise postpayment value plus the right-hand dividend atom. This exact identity bridges predictable Gaussian mesh coefficients with the postpayment-frozen stochastic source in the clipped four-event ledger. No Ito or reward inequality is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gsource15_original_leftlim_frozen_atom_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hXleft : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = X.X t ω) :
    Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (x + X.X t ω - rightLimit D t ω) +
        (rightLimit D t ω - D t ω) := by
  sorry
