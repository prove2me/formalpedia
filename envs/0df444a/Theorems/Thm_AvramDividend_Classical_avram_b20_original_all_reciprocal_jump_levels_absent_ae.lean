-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_original_all_reciprocal_jump_levels_absent_ae
-- name    : AvramDividend.Classical.avram_b20_original_all_reciprocal_jump_levels_absent_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T20:59:43.465276+00:00
-- url     : https://prove2.me/theorems/dc210ebe-1071-4d23-97a4-cdaf46b9961c
-- title:
--   Original Lévy sample paths avoid every reciprocal negative jump size at all integer horizons
-- statement:
--   On one full-measure event, all original sample paths avoid negative jumps with size exactly 1/(k+1) for every natural-number k and every integer horizon n. Standing bounded variation ensures diffuse Lévy marks. The theorem supplies the exact strict-versus-inclusive cutoff bridge required by the original finite-cutoff Laplace transform.
-- source:
--   Direct consequence of public Proved 60980559 (original a.e. countable reciprocal mark union nullity) and public Proved 2c942e8f (marked actual source count equals cardinality of the preimage). Does not assume the desired Laplace formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b20_original_all_reciprocal_jump_levels_absent_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (n k : ℕ) (v : ℝ≥0),
      0 < v → v ≤ (n : ℝ≥0) →
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω ≠
        (1 / ((k : ℝ) + 1)) := by sorry
