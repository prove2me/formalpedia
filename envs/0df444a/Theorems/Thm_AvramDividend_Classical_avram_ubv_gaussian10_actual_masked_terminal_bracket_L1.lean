-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:25:27.195828+00:00
-- url     : https://prove2.me/theorems/49dfbdc0-1303-447d-b992-1a2f6bc93c60
-- title:
--   Actual original masked Gaussian coefficient has integrable terminal quadratic bracket
-- statement:
--   On Avram's original finite probability measure, with the original spectrally negative Levy source, the original left-limit pre-payment reserve and the true Gaussian sigma-times-masked-gradient coefficient, establish integrability of its finite-horizon square bracket from a compact deterministic derivative bound, right-continuous original-filtration adaptedness, and finite time-window measure. Keep all other assumptions explicit; do not introduce a new Brownian process, completed filtration, or extra jump identities.
-- source:
--   Proved 9645ebf8 compact-band actual Gaussian bound; Proved 2616fc97 original adapted bracket; independent terminal-L1 child 99460b53; pinned Mathlib Filtration.le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_terminal_square_bracket_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) [SFinite μtime]
    (T : ℝ≥0) (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
      (G (t, ω)) ^ 2 ∂μtime) P := by sorry
