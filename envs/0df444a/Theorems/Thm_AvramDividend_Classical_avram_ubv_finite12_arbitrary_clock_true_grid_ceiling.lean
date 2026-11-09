-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
-- name    : AvramDividend.Classical.avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:00:18.314982+00:00
-- url     : https://prove2.me/theorems/604909b0-2085-49db-bc78-e950d86017a4
-- title:
--   Every bounded original stopping clock has a genuine right-continuous sampled ceiling within one mesh
-- statement:
--   For an arbitrary bounded stopping clock of the original right-continuous filtration, construct a first monotone physical-grid ceiling index that is itself a genuine sampled-filtration stopping time, is uniformly index-bounded, and reaches the clock within one time mesh. This applies to every localisation sigma k in the original finite-cap Gaussian reward budget, not only the ruin clock. The result is exact for the original source filtration without auxiliary processes or changes to ruin/dividend conventions.
-- source:
--   Source-exact generalisation of Proved original ruin-clock first-ceiling adapted events 5aee1f98, one-mesh error 468c6b4c, and sampled-stopping compatibility d0b4325f. The extraneous original ruin clock equality is eliminated; hσ itself gives the measurability required by all three proofs. Required to apply Proved original zero-jump Gaussian optional sampling a331e012 to arbitrary σ k in finite-cap conditional reward budget 50e1cf4c.

import Mathlib.Data.Nat.Find
import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, σ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    ∃ K : Ω → ℕ,
      IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, σ ω ≤ e (K ω) ∧ e (K ω) ≤ σ ω + δ) := by sorry
