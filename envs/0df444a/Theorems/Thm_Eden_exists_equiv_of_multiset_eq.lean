-- Prove2me | Theorems.Thm_Eden_exists_equiv_of_multiset_eq
-- name    : Eden.exists_equiv_of_multiset_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:32.161604+00:00
-- url     : https://prove2.me/theorems/424cc54a-6eb9-4d2b-9dc6-2995f1b561f4
-- title:
--   Eden: exists equiv of multiset eq
-- statement:
--   The Eden construction uses the exists equiv of multiset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L18-L25
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L18-L25

import Definitions.Def_Eden_Sorting
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Hom.PowersetCard
import Definitions.Def_Eden_SelectedSums
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exists_equiv_of_multiset_eq {n : ℕ} {a b : Fin n → ℝ}
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Fin n ≃ Fin n, ∀ i, b (e i) = a i := by sorry
