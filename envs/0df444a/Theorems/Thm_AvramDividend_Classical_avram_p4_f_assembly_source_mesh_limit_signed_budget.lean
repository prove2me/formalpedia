-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_mesh_limit_signed_budget
-- name    : AvramDividend.Classical.avram_p4_f_assembly_source_mesh_limit_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:16:34.778798+00:00
-- url     : https://prove2.me/theorems/0d3d812f-cc6c-4eb2-a4f7-cc96f98ac75d
-- title:
--   Original stopped Itô mesh upper bound and joint signed generator-control limit pass almost everywhere
-- statement:
--   An original-source limit assembly for the genuine stopped W, full Stieltjes Cash and discounted Term. Given a.e. finite-mesh Itô upper inequalities, jointly nonpositive finite-mesh generator/control residuals, and a.e. convergence of the three mesh variables to M,G,H, the accepted source stopped-mesh upper theorem transfers the full upper inequality, and closure of the nonpositive real half-line transfers G+H≤0. The source martingale L¹ and zero-mean obligations are separate and are not asserted here.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.11)-(5.13); accepted source upper mesh-limit theorem 4e28ddb7-45f7-4f84-bef5-baee4a4980e2; Mathlib Tendsto.add and le_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_stopped_ito_mesh_ae_limit_upper
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_source_mesh_limit_signed_budget
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
    (Mseq Gseq Hseq : ℕ → Ω → ℝ) (M G H : Ω → ℝ)
    (hupper : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Term ω + Cash ω ≤ w x + Mseq k ω + Gseq k ω + Hseq k ω)
    (hsign : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Gseq k ω + Hseq k ω ≤ 0)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Mseq k ω) atTop (𝓝 (M ω)) ∧
      Tendsto (fun k : ℕ => Gseq k ω) atTop (𝓝 (G ω)) ∧
      Tendsto (fun k : ℕ => Hseq k ω) atTop (𝓝 (H ω))) :
    (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
    (∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
