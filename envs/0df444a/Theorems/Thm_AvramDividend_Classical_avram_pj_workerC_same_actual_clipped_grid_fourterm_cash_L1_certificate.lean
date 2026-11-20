-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_same_actual_clipped_grid_fourterm_cash_L1_certificate
-- name    : AvramDividend.Classical.avram_pj_workerC_same_actual_clipped_grid_fourterm_cash_L1_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:34:46.230617+00:00
-- url     : https://prove2.me/theorems/227ac9f4-4786-4a05-9954-ab9c7ec52fef
-- title:
--   Actual original ruin-clipped stopped dividend clock has exact full physical four-term discounted Ito-Stieltjes mesh and vanishing L1 last-payment cash error on the same horizon
-- statement:
--   For the original admissible post-right dividend strategy, true ruin-clipped horizon τ and subordinate right-continuous stopping time ρ, the deterministic physical grid min(i*n/(m+1),ρ) reaches ρ exactly, and the exact four-term discounted Stieltjes telescoping identity for w of the original post-right reserve holds pathwise on every such mesh. The actual discounted payment-time Stieltjes cash discrepancy from the same last physical interval is integrable for all sufficiently fine meshes and vanishes in expected absolute value. Both are certified under identical true original Lévy and dividend data without adding any pathwise or stochastic assumptions.
-- source:
--   Proved b9dccb4b exact original true physical stopped four-term Stieltjes; 483ba6d9 cash mesh L1; edebe535 true clock horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclip_original_discount_cash_abs_mesh_eventual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_same_actual_clipped_grid_fourterm_cash_L1_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (w : ℝ → ℝ) (m : ℕ) (ω : Ω) :
    (let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω)))) ∧
    (let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε) := by sorry
