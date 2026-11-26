-- Prove2me | Theorems.Thm_Eden_ofFn_descending
-- name    : Eden.ofFn_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:24.389418+00:00
-- url     : https://prove2.me/theorems/61f15be9-3eb3-5d97-88df-e96556425785
-- title:
--   Eden: of Fn descending
-- statement:
--   The Eden construction uses the of Fn descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L97-L102
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L97-L102

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

theorem Eden.ofFn_descending {n : ℕ} (f : Fin n → ℝ) :
    List.ofFn (descending f) = (Finset.univ.val.map f).sort (· ≥ ·) := by sorry
