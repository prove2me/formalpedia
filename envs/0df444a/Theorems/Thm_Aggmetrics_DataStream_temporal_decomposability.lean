-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_temporal_decomposability
-- name    : Aggmetrics.DataStream.temporal_decomposability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:55:27.652548+00:00
-- url     : https://prove2.me/theorems/755a8e99-2258-4ea2-a3a8-1785df00a4da
-- title:
--   Data Stream: temporal decomposability
-- statement:
--   Theorem (Dynamic Temporal Preservation of Linear Decomposability): for a linear-fractional
--   measure `M(v) = ⟨a,v⟩ / ⟨b,v⟩` with canonical coefficient vectors `a b : Fin 4 → ℝ`, evaluated
--   on per-class contingency vectors `v j : Fin 4 → ℝ`, the micro-temporal composition equals the
--   denominator-weighted macro-temporal composition, exactly, at every timestamp.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L69-L74
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L69-L74

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.temporal_decomposability {m : ℕ} (hm : 0 < m) (a b : Fin 4 → ℝ) (v : Fin m → Fin 4 → ℝ)
    (hden : ∀ j, 0 < ∑ i, b i * v j i) :
    (∑ j, ∑ i, a i * v j i) / (∑ j, ∑ i, b i * v j i)
      = ∑ j, ((∑ i, b i * v j i) / ∑ l, ∑ i, b i * v l i)
          * ((∑ i, a i * v j i) / (∑ i, b i * v j i)) := by sorry
