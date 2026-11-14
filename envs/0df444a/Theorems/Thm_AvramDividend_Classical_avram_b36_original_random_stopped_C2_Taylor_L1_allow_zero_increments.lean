-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b36_original_random_stopped_C2_Taylor_L1_allow_zero_increments
-- name    : AvramDividend.Classical.avram_b36_original_random_stopped_C2_Taylor_L1_allow_zero_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:30:05.825734+00:00
-- url     : https://prove2.me/theorems/c496e810-b2e3-4f4b-a59d-83064c423b04
-- title:
--   Original stopped random physical C2 Taylor L1 energy estimate valid when some increments vanish
-- statement:
--   For a genuine original stopped Lévy finite mesh in a compact C2 interior reserve band, every sufficiently small physical increment, including zero increments, contributes to an integrable absolute Taylor error bounded in restricted expectation by epsilon times original quadratic energy. The former artificial assumption that every cell has nonzero source increment is removed.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), stopped Itô-Meyer; Proved original compact Taylor modulus, B27 random stopped L1 and B35 exact zero increment filtering.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
import Theorems.Thm_AvramDividend_Classical_avram_b35_original_physical_C2_Taylor_zero_increment_cell_filter_exact
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b36_original_random_stopped_C2_Taylor_L1_allow_zero_increments
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration ℝ≥0 mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (D : ℝ≥0 → Omega → ℝ) (hD : IsDividendStrategy F D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (A : Set Omega) (S : Finset ℕ)
        (s t : ℕ → Omega → ℝ≥0),
        let z : Omega → ℕ → ℝ := fun omega i =>
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u omega - rightLimit D u omega) (s i omega)
        let g : Omega → ℕ → ℝ := fun omega i =>
          X.X (t i omega) omega - X.X (s i omega) omega -
            (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
        let Q : Omega → ℝ := fun omega => ∑ i ∈ S, (g omega i) ^ 2
        let R : Omega → ℝ := fun omega => ∑ i ∈ S,
          (w (z omega i + g omega i) -
            taylorWithinEval w 1
              (Set.uIcc (z omega i) (z omega i + g omega i))
              (z omega i) (z omega i + g omega i) -
            (iteratedDeriv 2 w (z omega i) * (g omega i) ^ 2) / 2)
        (∀ i ∈ S, IsStoppingTime F.rightCont
          (fun omega => (s i omega : WithTop ℝ≥0))) →
        (∀ i ∈ S, IsStoppingTime F.rightCont
          (fun omega => (t i omega : WithTop ℝ≥0))) →
        (∀ᵐ omega ∂(P.restrict A), ∀ i ∈ S,
          z omega i ∈ Icc a b ∧ z omega i + g omega i ∈ Icc a b ∧
          dist (z omega i + g omega i) (z omega i) < delta) →
        AEStronglyMeasurable (fun omega => |R omega|) (P.restrict A) →
        IntegrableOn (fun omega => |R omega|) A P ∧
        (∫ omega in A, |R omega| ∂P) ≤
          eps * (∫ omega in A, Q omega ∂P) := by sorry
