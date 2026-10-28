-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_terminal_restricted_actual_grid_reversal_ws01a
-- name    : AvramDividend.Classical.chat04_terminal_restricted_actual_grid_reversal_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:59:44.078058+00:00
-- url     : https://prove2.me/theorems/2e976c5a-d183-4d6a-912f-522f9bf0002f
-- title:
--   Actual Levy finite-grid drawdown/minimum reversal jointly with a terminal-sum threshold
-- statement:
--   For genuine equal-mesh increments of a spectrally negative Levy law, restrict the finite-vector probability measure to paths whose terminal total sum is strictly below c. Under that actual endpoint-restricted measure, the strict finite-grid terminal drawdown and running minimum still have the exact reversal symmetry. This is a joint endpoint/extremum stochastic law, not a marginal reversal, an assumed Wiener-Hopf factorisation, or a killed-resolvent identity.
-- source:
--   Composes the canonically Proved levy_increment_vector_tilted_reversal (a712024a), fin_reverse_preserves_sum (6362f09e), and fin_vector_strict_drawdown_minimum_of_reversal_law (186f7ecf) on the actual endpoint indicator density.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.chat04_terminal_restricted_actual_grid_reversal_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (a c : ℝ) :
    (let ν : Measure (Fin n → ℝ) :=
       ((Measure.map (fun ω : Ω => fun i : Fin n =>
         X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
         (fun v : Fin n → ℝ =>
           if (∑ i : Fin n, v i) < c then (1 : ℝ≥0∞) else 0))
     let w : (Fin n → ℝ) → ℕ → ℝ :=
       fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
     ν {v : Fin n → ℝ | ∃ k : Fin n.succ,
       Finset.sum (Finset.range n) (w v) -
         Finset.sum (Finset.range k.val) (w v) < a} =
     ν {v : Fin n → ℝ | ∃ k : Fin n.succ,
       Finset.sum (Finset.range k.val) (w v) < a}) := by sorry
