-- Prove2me | Theorems.Thm_Eden_lipschitzWith_descending
-- name    : Eden.lipschitzWith_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:56.017745+00:00
-- url     : https://prove2.me/theorems/c3448876-8b1a-46fc-8a3e-2086da3f8d82
-- title:
--   Eden: lipschitz With descending
-- statement:
--   Descending sorting is 1-Lipschitz for the maximum metric on finite vectors.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L109-L117
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L109-L117

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

theorem Eden.lipschitzWith_descending (n : ℕ) :
    LipschitzWith 1 (descending : (Fin n → ℝ) → (Fin n → ℝ)) := by sorry
