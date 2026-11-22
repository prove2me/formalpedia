-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122
-- name    : AvramDividend.Classical.avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:08:38.090926+00:00
-- url     : https://prove2.me/theorems/9a9388b7-df7d-4bdf-b423-f21f30d9d4e8
-- title:
--   Original infinite-activity true ruin-clipped positive stopping clock: discounted full-dividend last-mesh absolute L1 error automatically vanishes
-- statement:
--   For the ORIGINAL spectrally negative Lévy dividend surplus, in either infinite or finite jump activity, let the canonical clipped ruin clock τ(ω)=min(ruinTime(ω), n).toNNReal and every genuine right-continuous stopping time σ_k satisfying σ_k≤τ. Prove the genuinely physical discounted full-dividend last-mesh error E_m(ω)=q Δ_m dividendMeasure(0,σ_k) + integral of exp(-q s) over the true last open interval (σ_k−Δ_m,σ_k) of paymentTimes closed at its right endpoint is eventually integrable in absolute value with expected |E_m|≤ε for any ε>0. Establish automatically σ_k≤n and σ_k≤ruinTime in extended time using the original proved exact clipping identity 079929e6, then apply the already PROVED full physical stopped cash error theorem 0c5ef385. No extra finite jump intensity or Gaussian restrictions. This explicitly resolves the stopped CASH boundary-L1 subcomponent of rootward Avram pathwise Ito–Meyer source 5e94ab55.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k : ℕ,
      let E : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let u : ℝ≥0 := σ k ω - Δ
        q * (Δ : ℝ) *
          (dividendMeasure D ω (Ioo (0 : ℝ) (σ k ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε := by sorry
