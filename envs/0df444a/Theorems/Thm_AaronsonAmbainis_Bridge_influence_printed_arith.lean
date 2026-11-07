-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_influence_printed_arith
-- name    : AaronsonAmbainis.Bridge.influence_printed_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:12.031825+00:00
-- url     : https://prove2.me/theorems/2fb8a336-b3aa-4e31-992c-4bbfe7b18b29
-- title:
--   Bridge: influence printed arith
-- statement:
--   The arithmetic of the printed form of the bound for the influences: for `V, K > 0`,
--   `0 ≤ L ≤ K` and `I ≥ 0`, the inequality `3 V^5 ≤ 3125 L² K^4 I²` gives `L > 0`,
--   `I ≥ (√15 / 125) V^{5/2} / (L K²)` and `I ≥ (√15 / 125) V^{5/2} / K³`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L117-L137
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L117-L137

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.influence_printed_arith {V K L I : ℝ} (hV : 0 < V) (hK : 0 < K) (hL0 : 0 ≤ L)
    (hLK : L ≤ K) (hI : 0 ≤ I) (h : 3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2) :
    0 < L ∧ Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / (L * K ^ 2) ≤ I ∧
      Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / K ^ 3 ≤ I := by sorry
