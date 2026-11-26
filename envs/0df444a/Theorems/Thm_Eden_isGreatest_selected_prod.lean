-- Prove2me | Theorems.Thm_Eden_isGreatest_selected_prod
-- name    : Eden.isGreatest_selected_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:33.713466+00:00
-- url     : https://prove2.me/theorems/540e12d5-e2d7-5a93-98c9-e3ba16211701
-- title:
--   Eden: is Greatest selected prod
-- statement:
--   The first k entries attain the largest k-fold product of any permutation of a
--   descending nonnegative vector, including ties and zero entries.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedProducts.lean#L34-L57
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedProducts.lean#L34-L57

import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_SelectedProducts
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.isGreatest_selected_prod {k n : ℕ} (hk : k ≤ n) {a b : Fin n → ℝ}
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    (hm : Finset.univ.val.map a = Finset.univ.val.map b) :
    IsGreatest {r : ℝ | ∃ s : Set.powersetCard (Fin n) k, r = ∏ j ∈ s.val, b j}
      (∏ i : Fin k, a (Fin.castLE hk i)) := by sorry
