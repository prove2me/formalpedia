-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys16_original_firstjump_zero_contact_grid_cash
-- name    : AvramDividend.Classical.avram_bv_phys16_original_firstjump_zero_contact_grid_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:25:30.136038+00:00
-- url     : https://prove2.me/theorems/91628ad0-d7c1-4a9e-ab7c-1204a842450d
-- title:
--   Original first-negative-jump strict zero-contact physical mesh has exact summed weighted cash
-- statement:
--   Under original finite-activity bounded variation and nonnegative drift, one common almost-sure event gives the exact weighted Stieltjes dividend cash sum over any finite ordered row of half-open physical cells, each strictly before the first negative source jump and identically zero in post-right-payment reserve. The equality holds cellwise with the same original dividend strategy. The first-negative-jump/ruin-straddling last cell is excluded and remains a separate ledger term.
-- source:
--   Required source-exact finite-mesh zero-contact contribution to 2bc848f9 and 4f605d76, from Proved ec4db783.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys16_original_firstjump_contact_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys16_original_firstjump_zero_contact_grid_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (m : ℕ),
      (∀ i, i < m →
        u i ≤ u (i + 1) ∧ u (i + 1) ≤ H ∧
        (u (i + 1) : WithTop ℝ≥0) <
          (⨅ v : ℝ≥0,
            if 0 < v ∧ X.X v ω -
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v < 0
            then (v : WithTop ℝ≥0) else ⊤) ∧
        (∀ v : ℝ≥0, u i ≤ v → v ≤ u (i + 1) →
          riskProcess X x D v ω -
            (rightLimit D v ω - D v ω) = 0)) →
      ∀ f : ℝ → ℝ≥0∞,
        (∑ i ∈ Finset.range m,
          ∫⁻ r in Ioc (u i : ℝ) (u (i + 1) : ℝ), f r
            ∂(dividendMeasure D ω)) =
        (∑ i ∈ Finset.range m,
          ∫⁻ r in Ioc (u i : ℝ) (u (i + 1) : ℝ), f r
            ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
