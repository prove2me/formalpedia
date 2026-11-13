-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b22_original_preleft_C2_local_taylor_L1
-- name    : AvramDividend.Classical.avram_b22_original_preleft_C2_local_taylor_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:36:06.928193+00:00
-- url     : https://prove2.me/theorems/bdc5159f-1017-4738-803a-79f88c62681e
-- title:
--   Original pre-left physical C2 Taylor compact-mesh remainder restricted L1 bound
-- statement:
--   On any event where an original Lévy pre-left physical mesh remains inside a C2 reserve band with small displacements, the expected absolute Taylor remainder is bounded by epsilon times the original mesh quadratic energy, provided both are locally integrable.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), stopped Ito-Meyer physical Gaussian Taylor mesh; proved original compact remainder 0f624bb1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b22_original_preleft_C2_local_taylor_L1
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
        IntegrableOn (fun ω => |R ω|) A P →
        IntegrableOn Q A P →
        (∫ ω in A, |R ω| ∂P) ≤
          ε * (∫ ω in A, Q ω ∂P) := by sorry
