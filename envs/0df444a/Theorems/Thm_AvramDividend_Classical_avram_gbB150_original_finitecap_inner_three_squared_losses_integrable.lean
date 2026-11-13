-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB150_original_finitecap_inner_three_squared_losses_integrable
-- name    : AvramDividend.Classical.avram_gbB150_original_finitecap_inner_three_squared_losses_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:34:24.645742+00:00
-- url     : https://prove2.me/theorems/bf5ecdec-3fa8-4fa7-bd68-6d3deb74b0d4
-- title:
--   Original finite-cap three fixed-time Gaussian squared errors integrable
-- statement:
--   Original fixed-time squared-loss integrability for all three K_m,K_p,H pairs, from proved joint measurability, mesh-wise bounds, real-time H bound, and B148. These are exactly the inner premises of B127.
-- source:
--   B135, B143, B145, B147, B148

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB150_original_finitecap_inner_three_squared_losses_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
      let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℝ := x + X.X s ω - rightLimit D s ω
        if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y ∈ Icc a b then deriv w Y else 1)
        else 0
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        (Finset.range (m + 1)).sum (fun i =>
          if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
          then G m i ω else 0)
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let H : ℝ → Ω → ℝ := fun t ω =>
        if Real.toNNReal t < ρ ω then
          Real.exp (-(q * t)) *
            (if x + X.X (Real.toNNReal t) ω -
                  rightLimit D (Real.toNNReal t) ω ∈ Icc a b
             then deriv w (x + X.X (Real.toNNReal t) ω -
                  rightLimit D (Real.toNNReal t) ω)
             else 1)
        else 0
      ∀ (m p : ℕ) (t : ℝ),
        Integrable (fun ω => (K m t ω - K p t ω) ^ 2) P ∧
        Integrable (fun ω => (K m t ω - H t ω) ^ 2) P ∧
        Integrable (fun ω => (H t ω - K p t ω) ^ 2) P := by sorry
