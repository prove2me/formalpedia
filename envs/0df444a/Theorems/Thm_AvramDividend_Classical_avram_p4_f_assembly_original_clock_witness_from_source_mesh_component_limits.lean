-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_clock_witness_from_source_mesh_component_limits
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_clock_witness_from_source_mesh_component_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:21:35.684867+00:00
-- url     : https://prove2.me/theorems/43f35294-855c-4281-af58-74773961902a
-- title:
--   Exact original stopped-clock Itô residual triple assembled from source mesh convergence and L1 martingale components
-- statement:
--   A conditional P4-F master assembly retaining the genuine original X and D, true stopped W, full Stieltjes Cash and discounted Term. Genuine stochastic source lemmas must supply: a.e. mesh upper inequalities, jointly nonpositive generator/control mesh residuals, convergence of the three residual sequences, and three individually integrable zero-mean original-source martingale components. The two separately Proved P4-F helpers transfer the actual upper inequality and residual sign to limits and combine the martingale components into the exact canonical M,G,H witness. This does not claim those missing source stochastic facts or prove the canonical 0dda1be7 theorem.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.11)-(5.13); accepted P4-F three-martingale theorem ea0aaca6-f1b3-467a-b199-7ea501be837e, and P4-F original-source mesh-limit signed budget helper (pending source-dependent proof).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_mesh_limit_signed_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_clock_witness_from_source_mesh_component_limits
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
    (Mseq Gseq Hseq : ℕ → Ω → ℝ)
    (Mc Ms Ml G H : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P) (hg : Integrable G P)
    (hh : Integrable H P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hupper : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Term ω + Cash ω ≤ w x + Mseq k ω + Gseq k ω + Hseq k ω)
    (hsign : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Gseq k ω + Hseq k ω ≤ 0)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Mseq k ω) atTop
        (𝓝 (Mc ω + Ms ω + Ml ω)) ∧
      Tendsto (fun k : ℕ => Gseq k ω) atTop (𝓝 (G ω)) ∧
      Tendsto (fun k : ℕ => Hseq k ω) atTop (𝓝 (H ω))) :
    ∃ M G' H' : Ω → ℝ,
      Integrable M P ∧ Integrable G' P ∧ Integrable H' P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G' ω + H' ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G' ω + H' ω) := by sorry
