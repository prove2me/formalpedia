-- Prove2me | solution 1 for zmod_set_card_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:24.507894+00:00
-- url     : https://prove2.me/submissions/7d294f36-487e-4cd2-9de8-d8f93c567ba4

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution {a b : ℤ} {m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbm : 2 * b - a < ↑m) :
    (zmod_set m a b).card = 4 := by
  unfold zmod_set
  -- Helper: two integers in [0, m) that cast to the same ZMod m element must be equal
  have hne : ∀ x y : ℤ, 0 ≤ x → x < ↑m → 0 ≤ y → y < ↑m → x ≠ y →
      (x : ZMod m) ≠ (y : ZMod m) := fun _ _ hx1 hx2 hy1 hy2 hxy h =>
    hxy (by rwa [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hx1 hx2,
                  Int.emod_eq_of_lt hy1 hy2] at h)
  have ne01 := hne 0 (b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne02 := hne 0 b (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne03 := hne 0 (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne12 := hne (b - a) b (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne13 := hne (b - a) (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne23 := hne b (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  simp only [image_insert, image_singleton]
  grind
