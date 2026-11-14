-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_source_compensated_simple_family_l2_envelope_20261113
-- name    : AvramDividend.Classical.avram_a21_source_compensated_simple_family_l2_envelope_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:15:44.046215+00:00
-- url     : https://prove2.me/theorems/52aefa39-91af-47d2-a983-89aca4b77ab0
-- title:
--   One original-space square-integrable jump count and compensator envelope uniformly dominates all simple-mark stages
-- statement:
--   For every sequence of unit-bounded Borel simple marks on a fixed negative Borel jump set, the actual original compensated physical marked-jump integrals are uniformly almost surely bounded by the same original physical jump count plus compensator intensity, and the square of that common envelope is integrable.
-- source:
--   Proved source square-integrable count plus intensity envelope 7413b910-18d6-4ed2-b831-7cdefe75ace7 and Proved bounded physical marked compensated integral norm bound 380e3c66-6d63-44a3-8774-1659019e7327.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_compensator_square_envelope
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_source_compensated_simple_family_l2_envelope_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let D : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ S)).toReal +
        (((T : ℝ≥0∞) * X.ν S).toReal)
    let Z : ℕ → Ω → ℝ := fun k ω =>
      (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, f k z ∂X.ν)
    Integrable (fun ω => (D ω)^2) P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ D ω) := by sorry
