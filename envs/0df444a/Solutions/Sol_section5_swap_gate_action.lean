-- Prove2me | solution 1 for section5_swap_gate_action
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:27.659803+00:00
-- url     : https://prove2.me/submissions/25c4254b-7f21-48c4-9541-f197d7adeb46

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5Routing
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution {m : ℕ} (i j : Fin m) (h : i ≠ j) (x : Qubits m) :
    act (embedOp (section5_swap_gate i j h).gate.mat (section5_swap_gate i j h).wires) (ket x) =
      ket (x ∘ Equiv.swap i j) := by
  classical
  ext y
  change Matrix.mulVec
    (embedOp (section5_swap_gate i j h).gate.mat (section5_swap_gate i j h).wires)
    (Pi.single x (1:ℂ)) y =
      (Pi.single (x ∘ Equiv.swap i j) (1:ℂ) : Qubits m → ℂ) y
  rw [Matrix.mulVec_single]
  simp only [MulOpposite.op_one, one_smul]
  change (if ∀ a : Fin m, a ∉ Set.range (Fin.cons i (fun _ : Fin 1 => j)) → y a=x a then
      (if y ∘ Fin.cons i (fun _ : Fin 1 => j)=
        section5_swap_two (x ∘ Fin.cons i (fun _ : Fin 1 => j)) then (1:ℂ) else 0)
      else 0) = (Pi.single (x ∘ Equiv.swap i j) (1:ℂ) : Qubits m → ℂ) y
  have hr (a : Fin m) : a ∉ Set.range (Fin.cons i (fun _ : Fin 1 => j)) ↔ a ≠ i ∧ a ≠ j := by
    simp [Fin.range_cons, Set.range_const, eq_comm]
  have hs : (y ∘ Fin.cons i (fun _ : Fin 1 => j)=
      section5_swap_two (x ∘ Fin.cons i (fun _ : Fin 1 => j))) ↔ y i=x j ∧ y j=x i := by
    constructor
    · intro hh
      exact ⟨congrFun hh 0,congrFun hh 1⟩
    · rintro ⟨h0,h1⟩
      ext k
      fin_cases k <;> simpa [section5_swap_two] using (by first | exact h0 | exact h1)
  have heq : ((∀ a : Fin m, a ∉ Set.range (Fin.cons i (fun _ : Fin 1 => j)) → y a=x a) ∧
      y ∘ Fin.cons i (fun _ : Fin 1 => j)=
        section5_swap_two (x ∘ Fin.cons i (fun _ : Fin 1 => j))) ↔ y=x ∘ Equiv.swap i j := by
    rw [hs]
    constructor
    · rintro ⟨hoff,hi,hj⟩
      funext a
      by_cases hai : a=i
      · subst a; simpa using hi
      by_cases haj : a=j
      · subst a; simpa using hj
      simpa [Equiv.swap_apply_of_ne_of_ne hai haj] using hoff a ((hr a).mpr ⟨hai,haj⟩)
    · intro hh
      subst y
      refine ⟨?_,by simp,by simp⟩
      intro a ha
      obtain ⟨hai,haj⟩ := (hr a).mp ha
      simp [Equiv.swap_apply_of_ne_of_ne hai haj]
  rw [← ite_and]
  simp only [heq]
  simp [Pi.single_apply]
