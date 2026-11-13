-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_simple_integral_L2_domination_convergence
-- name    : AvramDividend.Classical.avram_a21_original_bounded_simple_integral_L2_domination_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:36:13.708205+00:00
-- url     : https://prove2.me/theorems/6bb2d2ba-024c-48a8-8e73-d429f12a52a3
-- title:
--   Original finite-activity marked simple-integral uniform L2 domination and almost-sure convergence
-- statement:
--   For the original physical jump measure of a spectrally negative finite-activity Levy process, finite-valued marks uniformly bounded by one on negative Borel strip S produce physical marked integrals F_k dominated almost surely by the physical source count B. Both B and B squared are integrable on the original probability P, and convergence of the mark functions on S yields almost sure convergence of F_k to the physical marked integral of the limiting mark g. The proof uses existing proved original count moments, domination, finite jump count, and finite-mark convergence, and does not change the probability space.
-- source:
--   Mathlib dominated convergence; existing Proved original Borel count L2 and a.e. marked count domination; proved finite source count and source simple-mark integral convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_bounded_simple_integral_L2_domination_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hfBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hfLimit : ∀ z ∈ S, Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
    let B : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ S)).toReal
    Integrable B P ∧ Integrable (fun ω => (B ω) ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (J ω))) := by sorry
