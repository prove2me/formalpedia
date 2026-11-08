-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_initial_atom_grid_balance
-- name    : AvramDividend.Classical.avram_bv_stieltjes10_original_initial_atom_grid_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:19:47.330932+00:00
-- url     : https://prove2.me/theorems/3bdacdfd-0807-49f4-b367-345316634694
-- title:
--   Original time-zero Stieltjes atom balances every finite right-dividend grid
-- statement:
--   For any original admissible dividend strategy and finite sequence of sampled times starting at zero, the actual singleton Stieltjes payment at time zero equals the ENNReal of the total right-limit dividend increment corrected by the finite telescoping grid increments. No refinement, continuity or stochastic moment assumption is needed. The exact atom remains once.
-- source:
--   Algebraic finite-grid Stieltjes endpoint interface to the original dividendMeasure; compatible with the proved singleton formula 4f229f9a and the BV physical-grid HJB route 2bc848f9.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_stieltjes10_original_initial_atom_grid_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu0 : u 0 = 0) :
    dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal
        (rightLimit D (u n) ω - D 0 ω -
          ∑ i ∈ Finset.range n,
            (rightLimit D (u (i + 1)) ω -
              rightLimit D (u i) ω)) := by sorry
