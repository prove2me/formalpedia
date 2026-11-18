-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_fullcell_Hessian_cross_signed_integrable
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_fullcell_Hessian_cross_signed_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:29:36.352451+00:00
-- url     : https://prove2.me/theorems/1c5034a4-e7e8-4fcb-8769-0aa2428aefb1
-- title:
--   Original finitecap physical masked Hessian cross signed integrable each mesh
-- statement:
--   Signed integrability of the original physical fullcell Hessian correction, using proved absolute L1, exact coefficient and raw centered cross measurability. The rightLimit D, mask and mesh are unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_fullcell_Hessian_cross_signed_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) (j : ℕ) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w
                (x + X.X s ω - rightLimit D s ω) else 0) / 2 *
                  (R ^ 2 - Z ^ 2)
        else 0)
    ∀ m, Integrable (B m) P := by sorry
