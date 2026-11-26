-- Prove2me | Theorems.Thm_Eden_tendsto_descending
-- name    : Eden.tendsto_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:06.521425+00:00
-- url     : https://prove2.me/theorems/62d836ed-0b46-4c88-99d7-5199685e575e
-- title:
--   Eden: tendsto descending
-- statement:
--   The Eden construction uses the tendsto descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L123-L126
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L123-L126

import Definitions.Def_Eden_OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_Eden_Sorting
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_descending {n : ℕ} {f : ℝ → Fin n → ℝ} {a : Fin n → ℝ}
    (h : ∀ i, Tendsto (fun t => f t i) atTop (𝓝 (a i))) :
    Tendsto (fun t => descending (f t)) atTop (𝓝 (descending a)) := by sorry
