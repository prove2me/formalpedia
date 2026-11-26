-- Prove2me | Theorems.Thm_Eden_antitone_dist_le_of_matched_dist_le
-- name    : Eden.antitone_dist_le_of_matched_dist_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:33.208532+00:00
-- url     : https://prove2.me/theorems/43e02693-9e72-586b-b7a8-dd77c3b857d5
-- title:
--   Eden: antitone dist le of matched dist le
-- statement:
--   The Eden construction uses the antitone dist le of matched dist le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L66-L84
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Sorting.lean#L66-L84

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

theorem Eden.antitone_dist_le_of_matched_dist_le {n : ℕ} {a b f g : Fin n → ℝ} {δ : ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (haf : Finset.univ.val.map a = Finset.univ.val.map f)
    (hbg : Finset.univ.val.map b = Finset.univ.val.map g)
    (hfg : ∀ j, dist (f j) (g j) ≤ δ) (i : Fin n) : dist (a i) (b i) ≤ δ := by sorry
