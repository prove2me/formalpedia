-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_two_channel_ae_dominated_cash_bound_to_initial_condExp
-- name    : AvramDividend.Classical.avram_jump6_A_two_channel_ae_dominated_cash_bound_to_initial_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:58:34.504277+00:00
-- url     : https://prove2.me/theorems/2e326222-a63c-4237-beb4-fdc27b0c6122
-- title:
--   Two physical conditionally centred noise limits preserve stopped cash F0 upper
-- statement:
--   For an integrable stopped cash reward bounded by two finite-grid martingale gain channels and a vanishing pathwise error, integrably dominated channel limits inherit zero conditional expectation given the initial right-continuous filtration. The original reward has initial conditional expectation at most the HJB budget, without replacing conditional centring by unconditional mean zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_two_channel_ae_dominated_cash_bound_to_initial_condExp
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Flt : Filtration ℝ≥0 mOmega}
    (F : Omega → ℝ) (b : ℝ)
    (G J E : ℕ → Omega → ℝ)
    (MG MJ BG BJ : Omega → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGconv : ∀ᵐ omega ∂P,
      Tendsto (fun k => G k omega) atTop (𝓝 (MG omega)))
    (hJconv : ∀ᵐ omega ∂P,
      Tendsto (fun k => J k omega) atTop (𝓝 (MJ omega)))
    (hEconv : ∀ᵐ omega ∂P,
      Tendsto (fun k => E k omega) atTop (𝓝 (0 : ℝ)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ omega ∂P, ‖G k omega‖ ≤ BG omega)
    (hJdom : ∀ k, ∀ᵐ omega ∂P, ‖J k omega‖ ≤ BJ omega)
    (hG0 : ∀ k, P[G k | Flt.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hJ0 : ∀ k, P[J k | Flt.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hLedger : ∀ᵐ omega ∂P, ∀ k,
      F omega ≤ b + G k omega + J k omega + E k omega) :
    ∀ᵐ omega ∂P, P[F | Flt.rightCont 0] omega ≤ b := by sorry
