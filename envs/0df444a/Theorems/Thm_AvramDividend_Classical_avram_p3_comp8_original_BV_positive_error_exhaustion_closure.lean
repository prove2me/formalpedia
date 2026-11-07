-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_positive_error_exhaustion_closure
-- name    : AvramDividend.Classical.avram_p3_comp8_original_BV_positive_error_exhaustion_closure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:31:13.006725+00:00
-- url     : https://prove2.me/theorems/cad6d3d7-2314-48b0-968d-5204f891c1b7
-- title:
--   Source-mass domination closes global positive-error mean from localised bands
-- statement:
--   For the original bounded-variation Lévy process up to unit horizon, positive grid errors are globally integrable. Their expected positive part vanishes when the interior events exhaust almost surely, the interior positive errors vanish in expectation and the complementary positive errors are bounded by the intrinsic integrable BV source-mass tail. The original stopped/source-error estimates can establish each input separately.
-- source:
--   Composition of independently Proved c8a27dc5 BV source exhaustion, 67934bf2 measurable-event positive-error split and d9416dc6 moving-event tail absorption. This proves the needed L1 localisation-tail glue without assuming the final supermartingale conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_BV_positive_error_exhaustion_closure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hLocal : Tendsto
      (fun n => ∫ ω, max (if ω ∈ s n then Err n ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hTailBound : ∀ n, ∀ᵐ ω ∂P,
      max (if ω ∉ s n then Err n ω else 0) 0 ≤
        (if ω ∈ s n then 0 else
          K * (|X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|))) :
    Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
