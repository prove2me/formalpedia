-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b35_original_physical_C2_Taylor_zero_increment_cell_filter_exact
-- name    : AvramDividend.Classical.avram_b35_original_physical_C2_Taylor_zero_increment_cell_filter_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:41:57.104828+00:00
-- url     : https://prove2.me/theorems/4b70c2e2-5022-4bae-9619-1ece6f7cfece
-- title:
--   Original physical C2 Taylor stopped mesh equals sum restricted to nonzero drift-centred Lévy increments
-- statement:
--   At every original Lévy sample path and for any finite collection of random physical stopped clocks, the full sum of exact C2 Taylor remainders equals the same sum restricted to cells with nonzero original drift-centred source increment, since each zero-increment cell's remainder vanishes exactly.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i) stopped Itô-Meyer physical mesh; Mathlib taylorWithinEval_self.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b35_original_physical_C2_Taylor_zero_increment_cell_filter_exact
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration ℝ≥0 mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (D : ℝ≥0 → Omega → ℝ)
    (w : ℝ → ℝ) (S : Finset ℕ)
    (s t : ℕ → Omega → ℝ≥0) :
    ∀ omega : Omega,
      let z : ℕ → ℝ := fun i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u omega - rightLimit D u omega) (s i omega)
      let g : ℕ → ℝ := fun i =>
        X.X (t i omega) omega - X.X (s i omega) omega -
          (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
      let R : ℕ → ℝ := fun i =>
        (w (z i + g i) -
          taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
            (z i) (z i + g i) -
          (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)
      (∑ i ∈ S, R i) =
        (∑ i ∈ S.filter (fun i => g i ≠ 0), R i) := by sorry
