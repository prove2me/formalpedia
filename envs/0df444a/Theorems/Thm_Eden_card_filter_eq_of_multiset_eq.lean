-- Prove2me | Theorems.Thm_Eden_card_filter_eq_of_multiset_eq
-- name    : Eden.card_filter_eq_of_multiset_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:13.962564+00:00
-- url     : https://prove2.me/theorems/5dcb6735-bbfc-4d32-9dec-26341b634c53
-- title:
--   Eden: card filter eq of multiset eq
-- statement:
--   The Eden construction uses the card filter eq of multiset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L22-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L22-L28

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

theorem Eden.card_filter_eq_of_multiset_eq {n : ℕ} {f g : Fin n → ℝ}
    (hm : Finset.univ.val.map f = Finset.univ.val.map g) (p : ℝ → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun i => p (f i))).card =
      (Finset.univ.filter (fun i => p (g i))).card := by sorry
