-- Prove2me | solution 1 for section5_embedded_wire_permutation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:03:49.452711+00:00
-- url     : https://prove2.me/submissions/09781db8-4722-49d3-ae3c-2bd2fe6ab36a

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5Routing
import Mathlib
import Theorems.Thm_section5_swap_gate_action
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Explicit swap circuits for the outcome-dependent compaction in Theorem 5.4. -/



theorem section5_swapFactorsAux_length {α : Type*} [DecidableEq α]
    (l : List α) (p : Equiv.Perm α) (hp : ∀ {x}, p x ≠ x → x ∈ l) :
    (Equiv.Perm.swapFactorsAux l p hp).val.length ≤ l.length := by
  induction l generalizing p with
  | nil => simp [Equiv.Perm.swapFactorsAux]
  | cons x l ih =>
    unfold Equiv.Perm.swapFactorsAux
    split_ifs with h
    · have hp' : ∀ {y}, p y ≠ y → y ∈ l := by
        intro y hy
        exact List.mem_of_ne_of_mem (fun heq => by subst y; exact hy h.symm) (hp hy)
      exact (ih p hp').trans (Nat.le_succ _)
    · have hp' : ∀ {y}, (Equiv.swap x (p x)*p) y ≠ y → y ∈ l := by
        intro y hy
        have hne := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
        exact List.mem_of_ne_of_mem hne.2 (hp hne.1)
      exact Nat.succ_le_succ (ih _ hp')

theorem section5_permutation_short_swaps (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    ∃ l : List (Equiv.Perm (Fin p)), l.prod = σ ∧
      (∀ τ ∈ l, Equiv.Perm.IsSwap τ) ∧ l.length ≤ p := by
  let l := Equiv.Perm.swapFactors σ
  refine ⟨l.val,l.property.1,l.property.2,?_⟩
  have h := section5_swapFactorsAux_length (Finset.univ.sort (· ≤ ·)) σ
    (by intro x _; simp)
  simpa only [l, Equiv.Perm.swapFactors, Finset.length_sort,
    Finset.card_univ, Fintype.card_fin] using h







theorem section5_viaEmbedding_swap {p m : ℕ} (e : Fin p ↪ Fin m) (i j : Fin p) :
    (Equiv.swap i j).viaEmbedding e = Equiv.swap (e i) (e j) := by
  classical
  apply Equiv.ext
  intro a
  by_cases ha : a ∈ Set.range e
  · obtain ⟨b,rfl⟩ := ha
    rw [Equiv.Perm.viaEmbedding_apply]
    exact e.injective.map_swap i j b
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ha]
    have hi : a ≠ e i := by rintro rfl; exact ha ⟨i,rfl⟩
    have hj : a ≠ e j := by rintro rfl; exact ha ⟨j,rfl⟩
    exact (Equiv.swap_apply_of_ne_of_ne hi hj).symm

theorem section5_routing_act_mul {m : ℕ}
    (A B : Matrix (Qubits m) (Qubits m) ℂ) (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (A*B) ψ = act A (act B ψ) := by
  ext y
  exact congrFun (Matrix.mulVec_mulVec (WithLp.ofLp ψ) A B).symm y

theorem section5_swap_list_circuit {p m : ℕ} (e : Fin p ↪ Fin m)
    (l : List (Equiv.Perm (Fin p))) (hl : ∀ τ ∈ l, Equiv.Perm.IsSwap τ) :
    ∃ c : Circuit gates12 m, c.size ≤ l.length ∧
      ∀ x : Qubits m, act c.unitary (ket x) = ket (x ∘ l.prod.viaEmbedding e) := by
  classical
  induction l with
  | nil =>
    refine ⟨[],by simp [Circuit.size],?_⟩
    intro x
    have hp : (1 : Equiv.Perm (Fin p)).viaEmbedding e = 1 :=
      (Equiv.Perm.viaEmbeddingHom e).map_one
    simp [Circuit.unitary, act, List.prod_nil, hp]
  | cons τ l ih =>
    obtain ⟨c,hc,hact⟩ := ih (fun π hπ => hl π (List.mem_cons_of_mem τ hπ))
    obtain ⟨i,j,hij,rfl⟩ := hl τ List.mem_cons_self
    let g := section5_swap_gate (e i) (e j) (fun h => hij (e.injective h))
    refine ⟨g::c,Nat.succ_le_succ hc,?_⟩
    intro x
    have hu : Circuit.unitary (g::c) = c.unitary * embedOp g.gate.mat g.wires := by
      simp [Circuit.unitary, List.reverse_cons]
    rw [hu,section5_routing_act_mul,section5_swap_gate_action,hact]
    congr 1
    funext a
    rw [List.prod_cons]
    have hmul := (Equiv.Perm.viaEmbeddingHom e).map_mul (Equiv.swap i j) l.prod
    change (x ∘ Equiv.swap (e i) (e j) ∘ l.prod.viaEmbedding e) a =
      x (((Equiv.swap i j*l.prod).viaEmbedding e) a)
    rw [show ((Equiv.swap i j*l.prod).viaEmbedding e) =
      (Equiv.swap i j).viaEmbedding e*l.prod.viaEmbedding e from hmul,
      section5_viaEmbedding_swap]
    rfl

















end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution {p m : ℕ} (e : Fin p ↪ Fin m)
    (σ : Equiv.Perm (Fin p)) :
    ∃ c : Circuit gates12 m, c.size ≤ p ∧
      ∀ x : Qubits m, act c.unitary (ket x) = ket (x ∘ σ.viaEmbedding e) := by
  obtain ⟨l,hl,hls,hlen⟩ := section5_permutation_short_swaps p σ
  obtain ⟨c,hc,hact⟩ := section5_swap_list_circuit e l hls
  exact ⟨c,hc.trans hlen,by simpa only [hl] using hact⟩
