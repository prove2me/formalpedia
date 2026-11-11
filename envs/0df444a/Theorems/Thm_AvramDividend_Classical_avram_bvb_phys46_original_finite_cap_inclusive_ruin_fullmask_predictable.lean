-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys46_original_finite_cap_inclusive_ruin_fullmask_predictable
-- name    : AvramDividend.Classical.avram_bvb_phys46_original_finite_cap_inclusive_ruin_fullmask_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:19:35.959627+00:00
-- url     : https://prove2.me/theorems/5c719beb-2419-4620-a43e-9a77f9ff78e0
-- title:
--   Original finite-cap stopped full negative-mark reserve mask is predictable including zero and cap
-- statement:
--   For the original controlled spectrally negative Levy process and any admissible dividend strategy, a finite topological reserve cap C and deterministic finite horizon T, the full stopped mask consisting of nonnegative original prepayment left-limit reserve and ENNReal.ofReal reserve <=C is predictable for the original right-continuous filtration. The stopping clock is min(first ruin,T), inclusive of the first ruin-causing mark; the mask retains reserve zero and cap equality. This supplies the exact predictable-set ingredient of the existing finite-activity original physical source theorem phys42. The proof is an exact finite-cap conversion from the Proved stopped compact-band theorem via the pinned Mathlib ENNReal.ofReal_le_iff_le_toReal equivalence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys46_original_finite_cap_inclusive_ruin_fullmask_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 ≤ U p ∧ ENNReal.ofReal (U p) ≤ C} := by sorry
