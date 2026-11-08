-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_gaussian_stopped_quadratic_energy_L1
-- name    : AvramDividend.Classical.avram_ubv_top9_source_topcap_gaussian_stopped_quadratic_energy_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:18:08.335254+00:00
-- url     : https://prove2.me/theorems/464c5d00-1710-4fb1-8485-1b3fc44c2afa
-- title:
--   Original infinite-cap masked Gaussian gradient has integrable stopped quadratic energy
-- statement:
--   In the original infinite-cap Levy process, the compactly masked gradient at the exact left-limit pre-right-payment reserve has square-integrable time energy up to any genuine right-continuous stopping clock. The physical time-fibre quadratic-energy random variable is integrable. This is the original source Gaussian energy bridge for martingale arguments.
-- source:
--   Reuses original topcap predictable Gaussian finite L2 source ca1e7b57 and genuine predictable stopping time physical Fubini e7333410. Feeds the centred Gaussian term of physical witness 25573e81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_source_topcap_gaussian_stopped_quadratic_energy_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b) (hb : b < B)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0
    Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then (H (t, ω)) ^ 2 else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
