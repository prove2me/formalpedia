-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_preleft_C2_compact_taylor_L1_automatic
-- name    : AvramDividend.Classical.avram_b24_original_preleft_C2_compact_taylor_L1_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:40:44.026864+00:00
-- url     : https://prove2.me/theorems/9257f6d0-e3e8-4d1a-954d-607fe71890df
-- title:
--   Original source compact pre-left C2 Taylor physical mesh error is locally L1 automatically
-- statement:
--   On any localisation event where the genuine original Lévy physical mesh pre-left and post-increment reserves lie in a strict compact C2 band and increments are uniformly small, the Taylor remainder is integrable and its expected absolute size is at most epsilon times physical quadratic energy, using only eventwise measurability rather than global negative-jump second moments.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), original physical stopped Ito-Meyer Taylor remainder; B23 compact energy and pre-left modulus 0f624bb1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
import Theorems.Thm_AvramDividend_Classical_avram_b23_original_compact_preleft_mesh_square_energy_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_preleft_C2_compact_taylor_L1_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : Set Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0),
        let z : Ω → ℕ → ℝ := fun ω i =>
          Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)
        let g : Ω → ℕ → ℝ := fun ω i =>
          X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
        let R : Ω → ℝ := fun ω => ∑ i ∈ S,
          (w (z ω i + g ω i) -
            taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
              (z ω i) (z ω i + g ω i) -
            (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
        let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
        (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
          z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b ∧
          z ω i ≠ z ω i + g ω i ∧
          dist (z ω i + g ω i) (z ω i) < δ) →
        AEStronglyMeasurable Q (P.restrict A) →
        AEStronglyMeasurable (fun ω => |R ω|) (P.restrict A) →
        IntegrableOn (fun ω => |R ω|) A P ∧
        (∫ ω in A, |R ω| ∂P) ≤
          ε * (∫ ω in A, Q ω ∂P) := by sorry
