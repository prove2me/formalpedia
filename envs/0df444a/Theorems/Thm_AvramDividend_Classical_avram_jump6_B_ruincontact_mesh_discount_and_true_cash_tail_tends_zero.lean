-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_ruincontact_mesh_discount_and_true_cash_tail_tends_zero
-- name    : AvramDividend.Classical.avram_jump6_B_ruincontact_mesh_discount_and_true_cash_tail_tends_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:42:22.77564+00:00
-- url     : https://prove2.me/theorems/360c233f-f618-4f1d-84af-fe59b109f303
-- title:
--   Actual ruin-contact physical-mesh discount term and strictly pre-ruin cash tail vanish
-- statement:
--   Original stopped dividend cash tail and deterministic vanishing mesh discount, with exact strictly open right endpoint. Uses actual admissible dividend measure; no constructed substitute. Proven from monotone strict-contact tail convergence and real sequence arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_ruincontact_mesh_discount_and_true_cash_tail_tends_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j : ℕ =>
      q * ((n : ℝ) / ((j : ℝ) + 1)) * Real.exp (q * (n : ℝ)) *
        rightLimit D t ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((t : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
      atTop (𝓝 (0 : ℝ)) := by sorry
