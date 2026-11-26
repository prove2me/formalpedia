-- Prove2me | Theorems.Thm_Eden_isGreatest_selected_sum
-- name    : Eden.isGreatest_selected_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:29.822999+00:00
-- url     : https://prove2.me/theorems/71e3ee54-6964-4e25-904c-62213b131de7
-- title:
--   Eden: is Greatest selected sum
-- statement:
--   Among all k-element selections, the sum of the first k entries of any descending
--   rearrangement is the attained maximum.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L57-L79
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L57-L79

import Definitions.Def_Eden_Sorting
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Hom.PowersetCard
import Definitions.Def_Eden_SelectedSums
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.isGreatest_selected_sum {k n : ℕ} (hk : k ≤ n) {a b : Fin n → ℝ}
    (ha : Antitone a) (hm : Finset.univ.val.map a = Finset.univ.val.map b) :
    IsGreatest {r : ℝ | ∃ s : Set.powersetCard (Fin n) k, r = ∑ j ∈ s.val, b j}
      (∑ i : Fin k, a (Fin.castLE hk i)) := by sorry
