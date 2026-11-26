-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_mem_Icc
-- name    : BKAR.Forest.EdgeExtension.extendParam_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:12.715057+00:00
-- url     : https://prove2.me/theorems/a53662b0-f740-5f0b-b606-2e066c0992d3
-- title:
--   Edge Extension: extend Param mem Icc
-- statement:
--   The Edge Extension construction uses the extend Param mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L23-L32
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L23-L32

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}

theorem BKAR.Forest.EdgeExtension.extendParam_mem_Icc (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hs : 0 ≤ s ∧ s ≤ 1) (e' : F'.EdgeParam) :
    0 ≤ h.extendParam u s e' ∧ h.extendParam u s e' ≤ 1 := by sorry
