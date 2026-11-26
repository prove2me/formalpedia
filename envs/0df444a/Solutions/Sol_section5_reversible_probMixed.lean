-- Prove2me | solution 1 for section5_reversible_probMixed
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:38.288313+00:00
-- url     : https://prove2.me/submissions/ed977c5f-7ce1-4816-b083-0b47497019be

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
import Theorems.Thm_section5_basis_permutation_conjugation
import Theorems.Thm_section5_reversible_circuit_permutation
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Exact measurement laws for reversible classical post-processing. These hold
for arbitrary input matrices, so coherences between measurement transcripts do
not have to be discarded by an unproved intermediate-measurement assumption. -/



theorem section5_basis_permutation_probMixed {ι : Type} [Fintype ι] [DecidableEq ι]
    (U ρ : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (P : ι → Prop) [DecidablePred P] :
    probMixed U ρ P=∑ x : ι, if P (f x) then (ρ x x).re else 0 := by
  unfold probMixed
  rw [Finset.sum_filter,← Equiv.sum_comp f]
  simp only [section5_basis_permutation_conjugation U ρ f hact]







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution {m : ℕ} (c : Circuit gatesRev m)
    (ρ : Matrix (Qubits m) (Qubits m) ℂ) (P : Qubits m → Prop) [DecidablePred P] :
    ∃ f : Equiv.Perm (Qubits m),
      (∀ x, act c.unitary (ket x)=ket (f x)) ∧
      probMixed c.unitary ρ P=∑ x : Qubits m, if P (f x) then (ρ x x).re else 0 := by
  obtain ⟨f,hf⟩ := section5_reversible_circuit_permutation c
  exact ⟨f,hf,section5_basis_permutation_probMixed c.unitary ρ f hf P⟩
