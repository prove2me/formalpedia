-- Prove2me | solution 1 for section5_compaction_circuits
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:03.96352+00:00
-- url     : https://prove2.me/submissions/ccb9afce-ff21-42ed-b48a-45ca6b140506

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5Routing
import Mathlib
import Theorems.Thm_section5_embedded_wire_permutation
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Explicit swap circuits for the outcome-dependent compaction in Theorem 5.4. -/























theorem section5_particle_wire_permutation_apply (K s : ℕ) (σ : Equiv.Perm (Fin (2*K)))
    (r : Fin (2*K)) (b : Fin s) :
    section5_particle_wire_permutation K s σ (finProdFinEquiv (r,b)) =
      finProdFinEquiv (σ r,b) := by simp [section5_particle_wire_permutation]

theorem section5_particle_permutation_circuit {m K s : ℕ}
    (partEmb : Fin (2*K*s) ↪ Fin m) (σ : Equiv.Perm (Fin (2*K))) :
    ∃ c : Circuit gates12 m, c.size ≤ 2*K*s ∧
      ∀ x : Qubits m, act c.unitary (ket x) = ket (permPartReg54 partEmb σ x) := by
  obtain ⟨c,hc,hact⟩ := section5_embedded_wire_permutation partEmb
    (section5_particle_wire_permutation K s σ)
  refine ⟨c,hc,?_⟩
  intro x
  rw [hact]
  congr 1
  funext a
  by_cases ha : a ∈ Set.range partEmb
  · obtain ⟨k,rfl⟩ := ha
    obtain ⟨⟨r,b⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp [Equiv.Perm.viaEmbedding_apply,section5_particle_wire_permutation_apply]
  · simp only [Function.comp_apply,Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ha,
      permPartReg54_off partEmb σ x ha]

theorem section5_compaction_permutation (K : ℕ) (t : Qubits (2*K))
    (ht : K ≤ (Finset.univ.filter (fun j => t j=false)).card) :
    ∃ σ : Equiv.Perm (Fin (2*K)),
      ∀ k : Fin K, t (σ ⟨k.val,by omega⟩)=false := by
  classical
  let good : Finset (Fin (2*K)) := Finset.univ.filter (fun j => t j=false)
  have he : Nonempty (Fin K ↪ good) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin,Fintype.card_coe] using ht)
  obtain ⟨e⟩ := he
  let f : Fin K → Fin (2*K) := fun k => (e k).val
  let first : Fin K → Fin (2*K) := fun k => ⟨k.val,by omega⟩
  have hfirst : Function.Injective first := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (2*K) => z.val) hij)
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair first f hfirst hf
  refine ⟨σ,?_⟩
  intro k
  change t (σ (first k))=false
  rw [hσ k]
  exact (Finset.mem_filter.mp (e k).property).2







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution {m K s : ℕ}
    (partEmb : Fin (2*K*s) ↪ Fin m) :
    ∃ W : Qubits (2*K) → Circuit gates12 m,
      (∀ t, (W t).size ≤ 2*K*s) ∧
      ∀ t : Qubits (2*K), K ≤ (Finset.univ.filter (fun j => t j=false)).card →
        ∃ σ : Equiv.Perm (Fin (2*K)),
          (∀ k : Fin K, t (σ ⟨k.val,by omega⟩)=false) ∧
          ∀ x : Qubits m, act (W t).unitary (ket x) = ket (permPartReg54 partEmb σ x) := by
  classical
  have hchoice (t : Qubits (2*K)) :
      ∃ c : Circuit gates12 m, c.size ≤ 2*K*s ∧
        (K ≤ (Finset.univ.filter (fun j => t j=false)).card →
          ∃ σ : Equiv.Perm (Fin (2*K)),
            (∀ k : Fin K, t (σ ⟨k.val,by omega⟩)=false) ∧
            ∀ x : Qubits m, act c.unitary (ket x) = ket (permPartReg54 partEmb σ x)) := by
    by_cases ht : K ≤ (Finset.univ.filter (fun j => t j=false)).card
    · obtain ⟨σ,hσ⟩ := section5_compaction_permutation K t ht
      obtain ⟨c,hc,hact⟩ := section5_particle_permutation_circuit partEmb σ
      exact ⟨c,hc,fun _ => ⟨σ,hσ,hact⟩⟩
    · exact ⟨[],Nat.zero_le _,fun h => False.elim (ht h)⟩
  choose W hW using hchoice
  exact ⟨W,fun t => (hW t).1,fun t => (hW t).2⟩
