-- Prove2me | solution 1 for mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:49:06.251671+00:00
-- url     : https://prove2.me/submissions/09014b15-d105-4de8-828c-6165a7763077

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_common_paired_halving
import Theorems.Thm_mme_dwz_component_disallowed_word_mismatches_profile
import Theorems.Thm_mme_dwz_q6_121_211_component_even_length

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = MME.DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6))
    (hcoord : ∀ p,
      p.leftGrade =
        Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
          (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) :
    let labelGrade : LiftedCoarsePair.{u} 6 1 → Fin 3 :=
      fun p ↦ Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
        (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)
    (∀ (w : PowIndex (LiftedCoarsePair.{u} 6 1) N),
      (¬ ∀ a : Fin 3,
        Fintype.card {r : Fin N //
          (PowIndex.get N w r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) →
      ∀ p : Fin A × Fin H,
        ∃ r : Fin N,
          labelGrade (PowIndex.get N w r) ≠
            (family.entry p).1 0 (halving.position (Sum.inl r))) ∧
    (∀ (w : PowIndex (LiftedCoarsePair.{u} 6 1) N),
      (¬ ∀ a : Fin 3,
        Fintype.card {r : Fin N //
          (PowIndex.get N w r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) →
      ∀ p : Fin A × Fin H,
        ∃ r : Fin N,
          labelGrade (PowIndex.get N w r) ≠
            (family.entry p).1 1 (halving.position (Sum.inr r))) := by
  subst N
  let labelGrade : LiftedCoarsePair.{u} 6 1 → Fin 3 :=
    fun p ↦ Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
      (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)
  have hhalf : halving.half = 1036722900000000 * m := by
    have heven := halving.even_length
    have hcomponent :=
      mme_dwz_q6_121_211_component_even_length s hs m
    omega
  have hfirst (p : Fin A × Fin H) (a : Fin 3) :
      Fintype.card {r : Fin (MME.DWZTable2Counts.component s * m) //
        (family.entry p).1 0 (halving.position (Sum.inl r)) = a} =
          MME.DWZTable2Counts.split s a * m := by
    rw [halving.first_x p a]
    rcases hs with rfl | rfl <;>
      fin_cases a <;>
      simp [MME.DWZTable2Counts.split, hhalf]
  have hsecond (p : Fin A × Fin H) (a : Fin 3) :
      Fintype.card {r : Fin (MME.DWZTable2Counts.component s * m) //
        (family.entry p).1 1 (halving.position (Sum.inr r)) = a} =
          MME.DWZTable2Counts.split s a * m := by
    rw [halving.second_y p a]
    rcases hs with rfl | rfl <;>
      fin_cases a <;>
      simp [MME.DWZTable2Counts.split, hhalf]
  constructor
  · intro w hnot p
    exact mme_dwz_component_disallowed_word_mismatches_profile
      s m w hnot
      (fun r ↦ (family.entry p).1 0
        (halving.position (Sum.inl r)))
      (hfirst p) labelGrade hcoord
  · intro w hnot p
    exact mme_dwz_component_disallowed_word_mismatches_profile
      s m w hnot
      (fun r ↦ (family.entry p).1 1
        (halving.position (Sum.inr r)))
      (hsecond p) labelGrade hcoord
