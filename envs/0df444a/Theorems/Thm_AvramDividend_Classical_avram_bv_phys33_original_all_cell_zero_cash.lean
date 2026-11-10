-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys33_original_all_cell_zero_cash
-- name    : AvramDividend.Classical.avram_bv_phys33_original_all_cell_zero_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:24:55.4724+00:00
-- url     : https://prove2.me/theorems/38553237-61ff-4660-905d-e8128fbe92e7
-- title:
--   Original finite-activity BV zero-reserve cash identity on every physical cell, including a possible ruin-straddling cell
-- statement:
--   On a common full-measure event, every physical cell inside a bounded original horizon with zero postpayment reserve and no negative original source jumps has exact weighted Stieltjes dividend cash equal to drift-scaled Lebesgue cash, including cells on paths whose total horizon does not survive. In particular, intervals are half-open and left-end right-payment atoms are excluded. This is the source-exact cell interface for the finite-activity physical ledger, and holds for all weights, including the discounted weight.
-- source:
--   Direct specialisation of Proved bc78efba-a3bb-4269-ab9a-192e4303b30a to indexed original physical intervals, without assuming global survival or substituting an auxiliary process.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys33_original_all_cell_zero_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H)
    (u : ℕ → ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n i : ℕ,
      u n i ≤ u n (i + 1) →
      u n (i + 1) ≤ H →
      (∀ v : ℝ≥0, u n i ≤ v → v ≤ u n (i + 1) →
        riskProcess X x D v ω -
          (rightLimit D v ω - D v ω) = 0) →
      (∀ v : ℝ≥0, v ∈ Ioc (u n i) (u n (i + 1)) →
        X.X v ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) v = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc ((u n i : ℝ≥0) : ℝ) ((u n (i + 1) : ℝ≥0) : ℝ),
            f t ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc ((u n i : ℝ≥0) : ℝ) ((u n (i + 1) : ℝ≥0) : ℝ),
            f t ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
