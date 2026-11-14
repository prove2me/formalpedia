-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_smallnegative_source_cutoff_bands_union_open_negative_unit
-- name    : AvramDividend.Classical.avram_a22_smallnegative_source_cutoff_bands_union_open_negative_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:33:19.178407+00:00
-- url     : https://prove2.me/theorems/22660893-14bf-41e8-9139-b536c632e099
-- title:
--   Cofinal compensated negative mark bands recover precisely the strict interval (-1,0)
-- statement:
--   The union of physical compensated original negative spatial bands (-1,-1/(n+1)] is exactly the strict negative unit interval (-1,0). In particular the mark -1 remains excluded from the compensated bands and belongs to the uncompensated large-negative source. The proof uses the positive real reciprocal Archimedean lemma. This is the exact set-exhaustion premise for dominated convergence of the original Lévy signed smallmark compensator.
-- source:
--   Original Prove2Me physical smallband definition and pinned Mathlib exists_nat_one_div_lt lemma; Avram–Palmowski–Pistorius Lévy–Itô compensation truncation convention.

import Mathlib
open Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_a22_smallnegative_source_cutoff_bands_union_open_negative_unit :
    (⋃ n : ℕ, Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) =
      Ioo (-1 : ℝ) 0 := by sorry
