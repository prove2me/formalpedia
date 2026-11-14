-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b34_original_zero_length_clipped_source_C2_Taylor_cell_exact_zero
-- name    : AvramDividend.Classical.avram_b34_original_zero_length_clipped_source_C2_Taylor_cell_exact_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:38:45.400672+00:00
-- url     : https://prove2.me/theorems/170ed9f5-1003-47db-8008-2294d652e5ae
-- title:
--   Original zero-duration clipped Lévy physical C2 Taylor cells have identically zero remainder
-- statement:
--   For any finite collection of physical source cells where original stopped start and end clocks coincide on a sample, the sum of all full order-one C2 Taylor remainders for that original Lévy source and dividend reserve is exactly zero, with no regularity or jump-moment assumptions.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), degenerate last stopped mesh cell; Mathlib.Analysis.Calculus.Taylor.taylorWithinEval_self.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b34_original_zero_length_clipped_source_C2_Taylor_cell_exact_zero
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration ℝ≥0 mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (D : ℝ≥0 → Omega → ℝ)
    (w : ℝ → ℝ) (S : Finset ℕ)
    (s t : ℕ → Omega → ℝ≥0) :
    ∀ omega : Omega,
      (∀ i ∈ S, s i omega = t i omega) →
      (∑ i ∈ S,
        let z : ℝ :=
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u omega - rightLimit D u omega) (s i omega)
        let g : ℝ :=
          X.X (t i omega) omega - X.X (s i omega) omega -
            (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
        (w (z + g) -
          taylorWithinEval w 1 (Set.uIcc z (z + g)) z (z + g) -
          (iteratedDeriv 2 w z * g ^ 2) / 2)) = 0 := by sorry
