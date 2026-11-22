-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ripple_original_finitecap_fullcell_Hessian_cross_abs_L1_public
-- name    : AvramDividend.Classical.avram_ripple_original_finitecap_fullcell_Hessian_cross_abs_L1_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:00:25.115736+00:00
-- url     : https://prove2.me/theorems/47c7d5c5-be6b-4056-a8e9-9ab76f7245ad
-- title:
--   Public original zero-jump finite-cap physical stopped Hessian raw-centred cross vanishes in absolute L1
-- statement:
--   Prove absolute L1 vanishing of the real original finite-cap zero-jump stopped full-cell Hessian correction, using a publicly reusable original pre-ruin compact Hessian coefficient bound, fullcell integrability and original public Hessian raw-minus-centred square L1 convergence.
-- source:
--   Exact remotely Proved source of previously private theorem 2c6df43c-8e29-4afb-b140-3a6865e481e2; source-faithful public re-verification with only public upstream imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_fullcell_Hessian_cross_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_physical_Hessian_cross_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ripple_original_finitecap_fullcell_Hessian_cross_abs_L1_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
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
    Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
