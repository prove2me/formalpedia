-- Prove2me | Theorems.Thm_Erdos1219_mk_bounded_subsets_le
-- name    : Erdos1219.mk_bounded_subsets_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:25.969643+00:00
-- url     : https://prove2.me/theorems/937f4d40-d83c-4ee5-8283-b05e3c1cb94a
-- title:
--   Erdos1219: mk bounded subsets le
-- statement:
--   The subsets of `U` of cardinality `≤ μ`, when `#U ≤ 2 ^ μ`: there are at most `2 ^ μ`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L44-L63
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L44-L63

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.mk_bounded_subsets_le {V : Type u} (U : Set V) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hU : #U ≤ 2 ^ μ) : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ 2 ^ μ := by sorry
