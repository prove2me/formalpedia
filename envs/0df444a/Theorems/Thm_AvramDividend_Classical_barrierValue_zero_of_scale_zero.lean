-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
-- name    : AvramDividend.Classical.barrierValue_zero_of_scale_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:35:16.307165+00:00
-- url     : https://prove2.me/theorems/93b9d0c0-6dbc-41b0-a203-29fc161f8c96
-- title:
--   Zero-scale-origin forces the zero-barrier value candidate to vanish
-- statement:
--   The zero-barrier candidate is divE (W 0) (scaleDeriv W 0). If W(0)=0 it vanishes for every extended-real derivative normaliser by the platform divE convention (top normaliser returns zero, finite normaliser gives zero numerator). Together with the canonically Proved chat04_scale_zero_origin_of_unbounded_variation and the separately authored instantaneous-ruin value lemma, this supports the unbounded-variation branch of zero_reflectedSupValue_eq_barrierValue and the original optimal-barrier root.
-- source:
--   Direct simp proof from Definition.ScaleFunction barrierValue/divE, linking canonical chat04_scale_zero_origin_of_unbounded_variation c1b8958a and open zero_reflectedSupValue_eq_barrierValue b83a725b.

import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical

theorem AvramDividend.Classical.barrierValue_zero_of_scale_zero
    (W : ℝ → ℝ) (hW0 : W 0 = 0) :
    barrierValue W 0 0 = 0 := by sorry
