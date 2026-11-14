-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_family_disjoint_energy_20261113
-- name    : AvramDividend.Classical.avram_a21_original_simple_family_disjoint_energy_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:16:29.648203+00:00
-- url     : https://prove2.me/theorems/13f84cb2-fa79-4a74-b06b-e272871b1c17
-- title:
--   Uniform sequence of genuine original natural-index Borel marked jump stages and second moments
-- statement:
--   Given any sequence of uniformly bounded real finite-valued Borel marks on a negative Borel set, simultaneously choose for every approximation stage finitely many natural-indexed disjoint measurable physical mark fibres on the original Lévy process, with exact almost sure compensated physical integral identity and integrable square equal to the finite source energy.
-- source:
--   Proved original finite simple mark stage d3f5b266-dd21-4c98-8efb-849f40e9ced9, dependent countable choice; original Ω/P and physical marked measure. Supports the quantised Poisson parent 67336b2d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_nat_stage_exact_energy_20261112
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_family_disjoint_energy_20261113
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
    ∃ (K : ℕ → ℕ) (B : ℕ → ℕ → Set ℝ)
      (c : ℕ → ℕ → ℝ),
      let F : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (K k), c k i *
          ((NX ω (Ioc 0 T ×ˢ B k i)).toReal -
            (((T : ℝ≥0∞) * X.ν (B k i)).toReal))
      let E : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (K k), (c k i)^2 *
          (((T : ℝ≥0∞) * X.ν (B k i)).toReal)
      (∀ k, ∀ i ∈ Finset.range (K k),
        MeasurableSet (B k i) ∧ B k i ⊆ S) ∧
      (∀ k, ∀ i ∈ Finset.range (K k),
        ∀ j ∈ Finset.range (K k), i ≠ j →
          Disjoint (B k i) (B k j)) ∧
      (∀ k, ∀ᵐ ω ∂P, F k ω =
        (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, f k z ∂X.ν)) ∧
      (∀ k, Integrable (fun ω => (F k ω)^2) P) ∧
      (∀ k, (∫ ω, (F k ω)^2 ∂P) = E k) := by sorry
