-- Prove2me | solution 1 for inf_occ_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:42.069907+00:00
-- url     : https://prove2.me/submissions/5b8fbda3-01b8-466f-a96c-cebc6f05a4fc

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63


set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {X : Type*} (xs : Stream' X) (k : ℕ) :
    InfOcc (xs.drop k) = InfOcc xs := by
  ext x ; simp [InfOcc, frequently_atTop] ; constructor
  · intro h_inf n ; obtain ⟨m, h_m, rfl⟩ := h_inf n
    use (k + m) ; simp [get_drop'] ; omega
  · intro h_inf n ; obtain ⟨m, h_m, rfl⟩ := h_inf (n + k)
    use (m - k) ; simp [get_drop', (show n ≤ m - k by omega), (show k + (m - k) = m by omega)]
