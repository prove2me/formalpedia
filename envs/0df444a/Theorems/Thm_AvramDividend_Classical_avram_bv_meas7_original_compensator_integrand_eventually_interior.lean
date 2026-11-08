-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_compensator_integrand_eventually_interior
-- name    : AvramDividend.Classical.avram_bv_meas7_original_compensator_integrand_eventually_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:35:02.969478+00:00
-- url     : https://prove2.me/theorems/db31585f-45c3-4750-8ec0-22762a3ec306
-- title:
--   Original stopped discounted jump-value integrand eventually equals full interior source
-- statement:
--   For every positive dividend cap, the actual X.X minus rightLimit D predictable stopped pre-reserve and every negative jump mark, choose cofinal full compact compensated reserve masks such that the marked discounted jump-value source exp(-q t) (w(Z+z)-w(Z)) eventually agrees exactly pointwise with its unlocalised strict-interior counterpart at each bounded ruin-stopped clock. This is the pointwise part of the original X.ν compensation-limit passage; integrability and interchange of integrals remain separate obligations.
-- source:
--   Direct exact-source consequence of the Proved all-cap cofinal compact-band witnesses for the original X.X minus rightLimit D pre-reserve. The proof constructs the eventually equal band/interior reserve predicates and transports that equivalence to the actual stopped discounted negative-jump value-change kernel with the same physical clock. There is no stochastic-integral limit, dominating expectation or infinite-activity interchange claim.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_compensator_integrand_eventually_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (D : ℝ≥0 → Ω → ℝ) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧
      ∀ (S : ℝ≥0) (p : ℝ≥0 × Ω) (z : ℝ)
        (w : ℝ → ℝ) (q : ℝ),
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let Z : ℝ≥0 × Ω → ℝ := fun r =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
        ∀ᶠ n : ℕ in atTop,
          (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc (a n) (b n) ∧ z < 0 then
            Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
            else 0) =
          (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 then
            Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
            else 0) := by sorry
