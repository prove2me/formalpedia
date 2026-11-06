-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_full_atom_stopped_mesh_signed_mean_to_ennreal
-- name    : AvramDividend.Classical.avram_bv_env3_original_full_atom_stopped_mesh_signed_mean_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:40:11.55406+00:00
-- url     : https://prove2.me/theorems/77ffa1ad-405e-42cf-85d1-ca78365c195f
-- title:
--   Original BV full Stieltjes atom mesh witness and signed mean imply closed-horizon ENNReal cash bound
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy source and cap-admissible dividend strategy, a finite-mesh C1 signed witness with almost-sure source/compensator mesh convergence and integrable nonpositive expected signed residual implies the exact closed-horizon expected Stieltjes cash bound. The terminal is the original post-rightpayment reserve and includes the horizon atom. No independent process, equality in law or unproved stochastic identity is assumed. The open mathematical obligations are the concrete original stopped C1 mesh witness, convergence and signed mean.
-- source:
--   Pinned accepted source bridge: 60b39adb mesh limit; a849869c signed terminal integrability; 331f6956 exact nonnegative terminal; 67f2cfad real-to-ENNReal full Stieltjes cash. Parent c8770486 strict complement uses the Proved d6705e01 positive-horizon reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_full_atom_stopped_mesh_signed_mean_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (M B : Ω → ℝ) (Mmesh Bmesh : ℕ → Ω → ℝ)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if WithTop.some (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
       else 0) ≤ w x + Mmesh n ω + Bmesh n ω)
    (hMLim : ∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
