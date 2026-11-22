-- Prove2me | solution 1 for straussFunction_le_of_forall_mBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:01.353461+00:00
-- url     : https://prove2.me/submissions/b63a2aed-1658-4e60-982f-5e85704f2ccb

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_le_of_forall
import Theorems.Thm_hasPolychromColouring_mBound


set_option autoImplicit true
open Finset
theorem _root_.solution {k : ℕ} (hk : 4 ≤ k) : straussFunction k ≤ mBound k :=
  straussFunction_le_of_forall fun _ ↦ hasPolychromColouring_mBound hk
