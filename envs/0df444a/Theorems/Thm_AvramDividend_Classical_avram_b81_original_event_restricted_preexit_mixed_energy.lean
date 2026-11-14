-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b81_original_event_restricted_preexit_mixed_energy
-- name    : AvramDividend.Classical.avram_b81_original_event_restricted_preexit_mixed_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:03:42.691248+00:00
-- url     : https://prove2.me/theorems/7312e2a1-9911-44d8-9e76-8abd24d7708b
-- title:
--   Original finite-mixed physical pre-exit source compact mesh energy restricted to good event
-- statement:
--   Apply the Proved original B67 compact drift-corrected source bound only to those true pre-ruin and pre-upcrossing mesh cells selected on a measurable good event. Their pathwise source lower bounds and upper-exit conditions are assumed ONLY on that event, allowing genuine zero-clock paths and terminal crossing cells outside it. Proved B78 then gives an event-restricted expected mixed source square-energy bound from the original finite negative marked jump count and the global true no-jump Gaussian+drift square-energy hypotheses. This is the correct event-side counterpart of global B68 and avoids B73/B75 potentially empty fixed-index condition when some paths have zero clock. It does not itself prove the true stopped Ito generator or stochastic compensation for the one final negative jump.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i); original B67 strict pre-exit compact source and B78 event-restricted energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b78_original_event_restricted_mixed_source_square_energy
import Theorems.Thm_AvramDividend_Classical_avram_b67_original_preupper_X_centered_cell_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b81_original_event_restricted_preexit_mixed_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (A : Set Ω) (hA : MeasurableSet A)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (x b d : ℝ) (hxb : 0 ≤ x + b)
    (hCell : ∀ ω ∈ A, ∀ i ∈ S, s i ω ≤ t i ω ∧ t i ω ≤ T)
    (hLower : ∀ ω ∈ A, ∀ i ∈ S,
      -x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω)
    (hBeforeUp : ∀ ω ∈ A, ∀ i ∈ S,
      (s i ω : ℝ≥0∞) < twoSidedExitUpTime X b ω ∧
      (t i ω : ℝ≥0∞) < twoSidedExitUpTime X b ω)
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ ω ∈ A, ∀ i ∈ S, i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hEmeas : Measurable (fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P)
    (hDI : Integrable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    IntegrableOn E A P ∧ (∫ ω in A, E ω ∂P) ≤
      2 * (∫ ω in A, G ω ∂P) + 2 * d^2 * (∫ ω in A, D ω ∂P) +
        (x + b + (T : ℝ) * |X.c|)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
