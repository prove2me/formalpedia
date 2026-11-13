-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
-- name    : AvramDividend.Classical.avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:33:46.616687+00:00
-- url     : https://prove2.me/theorems/e15d4b15-4bf8-420f-a689-021791ae4418
-- title:
--   Exact original stopped strict discounted cash physical mesh error is integrable and its mean tends to zero
-- statement:
--   For the actual spectrally negative Levy X, original admissible dividend D and any right-continuous stopping time rho bounded by positive integer n, the intrinsic positive discounted cash discrepancy q Delta exp(q n) F plus the Stieltjes contact tail on (rho-Delta,rho) is integrable at every mesh row and converges to zero in expectation. This source-specific lemma is independent of the generator's global L1, finite-activity assumptions, and the spatial localisation; it reconciles the exact stopped cash ledger with increasingly fine physical grids.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger42_original_strict_discounted_cash_mesh_error_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger80_original_allmesh_strict_cash_error_integrable
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ)) := by sorry
