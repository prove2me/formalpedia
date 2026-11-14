-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
-- name    : AvramDividend.Classical.avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:25:37.704425+00:00
-- url     : https://prove2.me/theorems/07d9babe-b84c-418b-96ab-dee01966ed80
-- title:
--   Finite random grid occupied in at least one of countably many measurable source cutoff events has measurable real occupied-cell count
-- statement:
--   For an arbitrary measurable probability sample space, a finite set of grid cell indices and a countable family of measurable occupation predicates indexed by cutoff n and cell i, define the finite random occupied-cell index set by marking precisely those cells whose occupation event occurs at some cutoff. The real cardinal of this finite random set is measurable. The countable union of measurable cutoff occupation events is measurable for each cell, each real indicator is measurable, the sum over finitely many cells is measurable, and this sum exactly equals the finite occupied-set cardinal. This reusable formal measure-theoretic step is needed to pass from Proved original random-clock negative source Poisson finite cutoff count measurability B166 to the genuine uncut original physically marked-cell cardinal measurability, using physical source negative cutoff exhaustion B132 and exact marked Poisson count correspondence. No finite negative-mark moments or pathwise count finiteness are required.
-- source:
--   Mathlib measurableSet_iUnion, Finset.measurable_sum, Measurable.ite, Finset filter cardinal identity.

import Mathlib
open MeasureTheory Set Filter
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Finite-grid occupation by any countable family of measurable source cutoff events has a measurable real occupied-cell cardinal. -/

theorem AvramDividend.Classical.avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (S : Finset ℕ) (A : ℕ → ℕ → Ω → Prop)
    (hA : ∀ n i, MeasurableSet {ω : Ω | A n i ω}) :
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ n : ℕ, A n i ω)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry
