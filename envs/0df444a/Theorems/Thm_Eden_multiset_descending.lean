-- Prove2me | Theorems.Thm_Eden_multiset_descending
-- name    : Eden.multiset_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:36.869039+00:00
-- url     : https://prove2.me/theorems/8a638143-d9e5-57a5-a78b-3057d2c54772
-- title:
--   Eden: multiset descending
-- statement:
--   The Eden construction uses the multiset descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L104-L106
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L104-L106

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

theorem Eden.multiset_descending {n : ℕ} (f : Fin n → ℝ) :
    Finset.univ.val.map (descending f) = Finset.univ.val.map f := by sorry
