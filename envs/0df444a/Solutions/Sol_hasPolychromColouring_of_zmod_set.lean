-- Prove2me | solution 1 for hasPolychromColouring_of_zmod_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:40.186193+00:00
-- url     : https://prove2.me/submissions/f3927c3e-e489-40e3-9729-12f9e234e97a

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
import Theorems.Thm_HasPolychromColouring_of_image
import Theorems.Thm_hasPolychromColouring_fin_of_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_zmod
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution {a b c : ℤ} {m : ℕ}
    (hm_eq : (m : ℤ) = c - a + b)
    (h : HasPolychromColouring (Fin 3) (zmod_set m a b)) :
    HasPolychromColouring (Fin 3) ({0, a, b, c} : Finset ℤ) := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod m))
  change HasPolychromColouring (Fin 3) (({0, a, b, c} : Finset ℤ).image (Int.cast : ℤ → ZMod m))
  apply hasPolychromColouring_fin_of_le (by simp)
  rw [polychromNumber_zmod hm_eq]
  exact le_polychromNumber h
