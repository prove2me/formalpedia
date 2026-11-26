-- Prove2me | Theorems.Thm_Eden_antitone_le_of_matched_le
-- name    : Eden.antitone_le_of_matched_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:52.313831+00:00
-- url     : https://prove2.me/theorems/d236be44-70d2-4bae-823d-22616999b793
-- title:
--   Eden: antitone le of matched le
-- statement:
--   Pointwise upper bounds survive descending rearrangement.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L31-L64
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L31-L64

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

theorem Eden.antitone_le_of_matched_le {n : ℕ} {a b f g : Fin n → ℝ} {δ : ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (haf : Finset.univ.val.map a = Finset.univ.val.map f)
    (hbg : Finset.univ.val.map b = Finset.univ.val.map g)
    (hfg : ∀ j, f j ≤ g j + δ) (i : Fin n) : a i ≤ b i + δ := by sorry
