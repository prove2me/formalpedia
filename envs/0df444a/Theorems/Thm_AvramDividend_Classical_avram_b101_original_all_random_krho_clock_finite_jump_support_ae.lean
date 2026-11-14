-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b101_original_all_random_krho_clock_finite_jump_support_ae
-- name    : AvramDividend.Classical.avram_b101_original_all_random_krho_clock_finite_jump_support_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:50:59.962072+00:00
-- url     : https://prove2.me/theorems/b96906b8-afa1-4597-86e6-9d007832de08
-- title:
--   One original conull event has finitely many genuine negative source marks at every row of any random stopped clock family
-- statement:
--   Under finite original negative Levy activity, an already proved same-original-space result gives a single P-conull source event on which actual nonzero Levy jump times are finite up to every finite physical time. Therefore for an arbitrary countable sequence of true random sample-path clocks κ(k,ω), every row k has only finitely many genuine original jump times in (0,κ(k,ω)] simultaneously on that same conull event. No new null-set intersections, localisation assumptions or global negative second moments are needed. This feeds the actual spatially clipped stopping-clock source decomposition in Proposition 4(i).
-- source:
--   Proved avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae, original spectrally negative Levy finite-activity source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The same conull original-source event controls all actual spatially clipped random stopping clocks. -/

theorem AvramDividend.Classical.avram_b101_original_all_random_krho_clock_finite_jump_support_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      {u : ℝ≥0 | 0 < u ∧ u ≤ κ k ω ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}.Finite := by sorry
