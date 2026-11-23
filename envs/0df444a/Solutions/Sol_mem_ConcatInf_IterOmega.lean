-- Prove2me | solution 1 for mem_ConcatInf_IterOmega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:01.051935+00:00
-- url     : https://prove2.me/submissions/8646fd46-3801-4c22-b9d8-d828761e1c93

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_P2M_Stream__extract_append_zero_right_6dd07cb04cbe
import Theorems.Thm_P2M_Stream__extract_apppend_right_right_39982fde78ca
import Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260


set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L0 L1 : Set (List A)} {as : Stream' A}
    (h : as ∈ L0 * L1^ω) : ∃ φ : Stream' ℕ, StrictMono φ ∧
      as.extract 0 (φ 0) ∈ L0 ∧ ∀ m, as.extract (φ m) (φ (m + 1)) ∈ L1 := by
  obtain ⟨al0, as1, h_al0, ⟨φ1, h_mono, h_φ1_0, h_φ1_sub⟩, rfl⟩ := h
  use (fun m ↦ φ1 (m) + al0.length)
  constructorm* _ ∧ _
  · intro m n h_mn ; have := h_mono h_mn ; grind
  · simp [h_φ1_0, h_al0, extract_append_zero_right, extract_eq_nil]
  · intro m
    have h1 : φ1 (m + 1) + al0.length - (φ1 m + al0.length) = φ1 (m + 1) - φ1 m := by omega
    specialize h_φ1_sub m
    simpa (disch := omega) [extract_apppend_right_right]
