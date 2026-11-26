-- Prove2me | Theorems.Thm_Eden_descending_antitone
-- name    : Eden.descending_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:47.148999+00:00
-- url     : https://prove2.me/theorems/bc22255d-3414-482b-9a4e-ef49249ac3a8
-- title:
--   Eden: descending antitone
-- statement:
--   The Eden construction uses the descending antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L91-L95
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L91-L95

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

theorem Eden.descending_antitone {n : ℕ} (f : Fin n → ℝ) : Antitone (descending f) := by sorry
