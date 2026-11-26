-- Prove2me | Theorems.Thm_Eden_continuous_descending
-- name    : Eden.continuous_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:49.554541+00:00
-- url     : https://prove2.me/theorems/af79308e-2504-4b07-9bf7-4ce60f0b6c3e
-- title:
--   Eden: continuous descending
-- statement:
--   The Eden construction uses the continuous descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L119-L121
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L119-L121

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

theorem Eden.continuous_descending (n : ℕ) :
    Continuous (descending : (Fin n → ℝ) → (Fin n → ℝ)) := by sorry
