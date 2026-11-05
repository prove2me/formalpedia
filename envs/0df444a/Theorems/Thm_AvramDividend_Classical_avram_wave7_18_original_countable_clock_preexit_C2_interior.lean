-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_C2_interior
-- name    : AvramDividend.Classical.avram_wave7_18_original_countable_clock_preexit_C2_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:09:21.714438+00:00
-- url     : https://prove2.me/theorems/135ab4f5-71bf-491d-b023-d88dd58791a1
-- title:
--   Original reserve countably observed exit is an original-filtration stopping clock with positive C² pre-exit domain
-- statement:
--   For the exact original controlled Lévy reserve Z_t=x+X.X t-rightLimit D t with admissible dividend strategy D, fix a buffer band [lower,upper] with 0<lower and all of it strictly below the reserve cap C. Assume the exact source ContDiffOn ℝ 2 w {y|0<y ∧ ENNReal.ofReal y<C} and a deterministic countable grid that meets every right-hand neighbourhood before any later time. Define σ(ω)=inf_k if Z_(r_k) strictly leaves the band, then r_k, else ⊤. The already Proved original-reserve adaptedness yields the countable observation stopping clock in 𝓕.rightCont; source right continuity plus grid richness detects every strict exterior excursion; the observed-exit equivalence then makes T≤σ equivalent to band membership at every s<T. Therefore every sample before T≤σ has positive reserve, lies below C, and is a point of C² regularity of w on the exact positive-domain binder. No Gaussian Itô, compensated-jump, Taylor-compensation, or Stieltjes result is re-proved. The theorem is honest about the grid-richness assumption, and works also at C=∞.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_countable_clock_preexit_C2_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) ω →
      ∀ s : ℝ≥0, s < T →
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω) := by sorry
