-- Prove2me | solution 1 for folded_query_in_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:03:30.86672+00:00
-- url     : https://prove2.me/submissions/5166dab2-bf7e-4184-ae25-f58bbedea113

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (z : F) (hz : z ∈ P.D_0) (i : ℕ) :
    i ≤ P.num_foldings → folded_query P z i ∈ FRI_domain P i := by
  induction i generalizing z with
  | zero => exact fun _ ↦ hz
  | succ i ih =>
    intro hi
    simp only [FRI_domain, folded_query]
    split_ifs with h
    · simp only [pow_domain, Finset.mem_image]
      exact ⟨_, ih z hz (Nat.le_of_succ_le hi), rfl⟩
    · omega
