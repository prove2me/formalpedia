-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_deterministic_killed_qscale
-- name    : AvramDividend.Classical.avram_root29_01_deterministic_killed_qscale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:25:13.44433+00:00
-- url     : https://prove2.me/theorems/094049ef-e9e7-46f4-b55f-5f760a85dc10
-- title:
--   Authentic original-Lévy deterministic killed q-scale harmonic semigroup at all real reserves
-- statement:
--   For an actual original-P spectrally negative Lévy process, any positive q-root and genuine scale function, the real expectation of exp(-qt)W(x+X_t) on the actual closed nonnegative historical survival event through every finite deterministic t equals W(x), at every real reserve including zero. Uses the genuine original-P perpetual Esscher killed Markov identity and the genuine all-real real-valued survival-scale identity; cancels the positive Esscher factor by exact real exponential algebra, with no assumed stopped exit or optional stopping.
-- source:
--   WS1A draft work/avram_root29_01_deterministic_killed_qscale_draft.lean, logically downstream of source-specific 1f7a50c5 and 6dc4855b. Do not submit until both are canonically Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_perpetual_survival_markov
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_perpetual_survival_scale_real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_root29_01_deterministic_killed_qscale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) =
      W x := by sorry
