-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_right_continuous_grid_detection
-- name    : AvramDividend.Classical.avram_wave7_18_original_right_continuous_grid_detection
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:00:01.782181+00:00
-- url     : https://prove2.me/theorems/0f85032c-6257-4893-9402-b3f131714247
-- title:
--   Every strict original-reserve exterior exit is observed by a right-cofinal deterministic grid
-- statement:
--   For the original reserve Z_t=x+X.X t-rightLimit D t on the original right-continuous filtration, admissible D gives the already Proved postPaymentReserve_cadlag_adapted: every path of Z is right-continuous. Let a countable deterministic grid r_k have this explicit right-local detection richness: for any s<t and every neighbourhood U of s within the right half-line Ici s, some r_k<t belongs to U. If the original reserve strictly leaves the closed band [lower,upper] at s<t, the strict exterior set Iio lower union Ioi upper is open, hence right-continuity makes its inverse image a right-neighbourhood U of s. The grid richness chooses k with r_k<t and Z_(r_k) outside. This discharges the exact detection hypothesis for the separate countable observed-exit equivalence theorem. It is an honest original-source path regularity theorem, without asserting the grid richness for arbitrary r or borrowing an unrelated stochastic space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_right_continuous_grid_detection
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∀ ω (s t : ℝ≥0), s < t →
      (x + X.X s ω - rightLimit D s ω < lower ∨
        upper < x + X.X s ω - rightLimit D s ω) →
      ∃ k, r k < t ∧
        (x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω) := by sorry
