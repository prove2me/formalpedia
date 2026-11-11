-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
-- name    : AvramDividend.Classical.avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:24:35.340331+00:00
-- url     : https://prove2.me/theorems/67f4c9ea-3d46-4f34-b400-549b16a82a19
-- title:
--   Original finite-cap full stopped reward mask is predictable with bounded prestate
-- statement:
--   The original finite-horizon, strictly preterminal and inclusively ruin-stopped BV dividend mark mask, including zero and cap-contact reserve values, is predictable. On this mask the original left-limit reserve is bounded above by the real cap. This is the exact missing event and cap premise for the Proved original physical compensator fibre L1 theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    ∀ n : ℕ,
      let E : Set (ℝ≥0 × Ω) := {p |
        0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
      MeasurableSet[𝓕.rightCont.predictable] E ∧
        ∀ p ∈ E, U p.1 p.2 ≤ C.toReal := by sorry
