-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_L1_joint_localisation_witness
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_L1_joint_localisation_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:48:32.620565+00:00
-- url     : https://prove2.me/theorems/73697817-17ad-4d1b-9a73-172b2b032e45
-- title:
--   Original stopped Ito signed-residual witnesses from dominated aggregate source localisation without separate component L1
-- statement:
--   For the actual original source X, admissible-control stopping W, full Stieltjes Cash and discounted Term, an aggregate localised martingale residual sequence with exact mean zero, individual measurable limits, integrable dominating envelopes for aggregate M/G/H, signed finite-stage generator-control residuals and genuine finite-mesh pathwise upper bounds yields the exact integrable M,G,H conclusion. It relies on separately accepted source localisation and mesh-limit theorems. It does not insert any of those bounds into the canonical original 0dda theorem or claim its stochastic calculus is complete.
-- source:
--   Accepted P4-E original joint stopped L1 mean and signed limit 2479bab2-8ebf-48e0-9094-f6ceeafa1371 and P4-F source mesh limit 0d3d812f-cc6c-4eb2-a4f7-cc96f98ac75d; Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_stopped_L1_mean_and_signed_limit
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_mesh_limit_signed_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_L1_joint_localisation_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mseq Gseq Hseq : ℕ → Ω → ℝ) (M G H BM BG BH : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mseq k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hGMeas : AEStronglyMeasurable G P)
    (hHMeas : AEStronglyMeasurable H P)
    (hBMInt : Integrable BM P) (hBGInt : Integrable BG P)
    (hBHInt : Integrable BH P)
    (hMBound : ∀ k, ∀ᵐ ω ∂P, ‖Mseq k ω‖ ≤ BM ω)
    (hGBound : ∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω)
    (hHBound : ∀ k, ∀ᵐ ω ∂P, ‖Hseq k ω‖ ≤ BH ω)
    (hCentred : ∀ k, (∫ ω, Mseq k ω ∂P) = 0)
    (hUpper : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Term ω + Cash ω ≤ w x + Mseq k ω + Gseq k ω + Hseq k ω)
    (hSign : ∀ᵐ ω ∂P, ∀ k : ℕ, Gseq k ω + Hseq k ω ≤ 0)
    (hConv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Mseq k ω) atTop (𝓝 (M ω)) ∧
      Tendsto (fun k : ℕ => Gseq k ω) atTop (𝓝 (G ω)) ∧
      Tendsto (fun k : ℕ => Hseq k ω) atTop (𝓝 (H ω))) :
    ∃ M' G' H' : Ω → ℝ,
      Integrable M' P ∧ Integrable G' P ∧ Integrable H' P ∧
      (∫ ω, M' ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G' ω + H' ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M' ω + G' ω + H' ω) := by sorry
