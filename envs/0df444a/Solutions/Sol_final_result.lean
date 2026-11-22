-- Prove2me | solution 1 for final_result
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:41:27.843808+00:00
-- url     : https://prove2.me/submissions/e8691364-d2c0-425b-9105-f79a17a21fa7

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Compute
import Definitions.Def_Polychromatic_FourThree_Combi
import Definitions.Def_Polychromatic_Main
import Theorems.Thm_allC_289
import Theorems.Thm_normal_bit
import Theorems.Thm_suffices_cases
import Theorems.Thm_suffices_flip
import Theorems.Thm_suffices_gcd
import Theorems.Thm_suffices_minimal
import Theorems.Thm_suffices_nat
import Theorems.Thm_suffices_triple


set_option autoImplicit true

theorem _root_.solution (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S :=
-- ANCHOR_END: final
  suffices_minimal
    (suffices_triple
      (suffices_flip
        (suffices_gcd
          (suffices_cases _
            (suffices_nat _ allC_289)
          normal_bit)))) _ hS
