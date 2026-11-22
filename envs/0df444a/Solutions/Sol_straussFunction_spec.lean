-- Prove2me | solution 1 for straussFunction_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:48:49.026005+00:00
-- url     : https://prove2.me/submissions/1c438c6f-39c0-41b8-878c-d24bcfd79654

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_exists_colouring_of_sq_le

section
open Finset
private lemma straussFunction_nonempty {k : ℕ} (hk : k ≠ 0) :
    {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}.Nonempty := by
  use 3 * k ^ 2
  intro S hS
  exact exists_colouring_of_sq_le hk (S := S) hS
open Asymptotics Filter
end

set_option autoImplicit true
open Finset
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) (S : Finset ℤ)
    (hkS : straussFunction k ≤ #S) :
    HasPolychromColouring (Fin k) S :=
  Nat.sInf_mem (straussFunction_nonempty hk) S hkS
