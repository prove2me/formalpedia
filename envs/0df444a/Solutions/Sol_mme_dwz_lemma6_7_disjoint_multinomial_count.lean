-- Prove2me | solution 1 for mme_dwz_lemma6_7_disjoint_multinomial_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:08:48.312283+00:00
-- url     : https://prove2.me/submissions/1274248c-7eb1-4f39-8796-00ce08879741

import Mathlib
import Definitions.Def_mme_dwz_prescribed_splits

open scoped BigOperators
set_option autoImplicit false

namespace MME.DWZCompatibilityCount

def orderedMultinomial : List ℕ → ℕ
  | [] => 1
  | c :: cs => (c + cs.sum).choose c * orderedMultinomial cs

@[simp] theorem orderedMultinomial_nil : orderedMultinomial [] = 1 := rfl

@[simp] theorem orderedMultinomial_cons (c : ℕ) (cs : List ℕ) :
    orderedMultinomial (c :: cs) =
      (c + cs.sum).choose c * orderedMultinomial cs := rfl

theorem orderedMultinomial_spec (cs : List ℕ) :
    (cs.map Nat.factorial).prod * orderedMultinomial cs = cs.sum.factorial := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons,
        orderedMultinomial_cons]
      rw [mul_assoc, mul_left_comm (cs.map Nat.factorial).prod,
        ← mul_assoc c.factorial, ih]
      rw [mul_comm c.factorial, mul_assoc]
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Nat.add_choose_mul_factorial_mul_factorial cs.sum c

theorem orderedMultinomial_eq_multinomial (cs : List ℕ) :
    orderedMultinomial cs =
      Nat.multinomial Finset.univ (fun i : Fin cs.length => cs.get i) := by
  refine Nat.eq_of_mul_eq_mul_left
    (n := (cs.map Nat.factorial).prod) (by
      apply List.prod_pos
      intro n hn
      rcases List.mem_map.1 hn with ⟨k, hk, rfl⟩
      exact Nat.factorial_pos k) ?_
  rw [orderedMultinomial_spec]
  symm
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin cs.length))
    (fun i : Fin cs.length => cs.get i)
  simpa [← List.prod_ofFn, ← List.sum_ofFn] using h

theorem card_prescribedSplits
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (cs : List ℕ)
    (hsize : cs.sum = S.card) :
    Nat.card (PrescribedSplits S cs) = orderedMultinomial cs := by
  induction cs generalizing S with
  | nil =>
      simp only [List.sum_nil] at hsize
      simp [PrescribedSplits, orderedMultinomial]
  | cons c cs ih =>
      simp only [List.sum_cons] at hsize
      rw [show Nat.card (PrescribedSplits S (c :: cs)) =
          ∑ T : ↥(S.powersetCard c),
            Nat.card (PrescribedSplits (S \ (T : Finset ι)) cs) by
            simp only [PrescribedSplits]
            letI := Fintype.ofFinite (PrescribedSplits S (c :: cs))
            letI (T : ↥(S.powersetCard c)) :=
              Fintype.ofFinite (PrescribedSplits (S \ (T : Finset ι)) cs)
            simpa only [Nat.card_eq_fintype_card] using
              (@Fintype.card_sigma ↥(S.powersetCard c)
                (fun T : ↥(S.powersetCard c) =>
                  PrescribedSplits (S \ (T : Finset ι)) cs) _ _)]
      have hlocal (T : ↥(S.powersetCard c)) :
          Nat.card (PrescribedSplits (S \ (T : Finset ι)) cs) =
            orderedMultinomial cs := by
        apply ih
        have hTmem := T.property
        rw [Finset.mem_powersetCard] at hTmem
        rw [Finset.card_sdiff_of_subset hTmem.1, hTmem.2]
        omega
      simp_rw [hlocal]
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard]
      rw [orderedMultinomial_cons]
      congr 2
      exact congrArg (fun n => n.choose c) hsize.symm

end MME.DWZCompatibilityCount

open MME.DWZCompatibilityCount

theorem solution
    {R : Type*} [Fintype R]
    (Position : R → Type*)
    [∀ r, Fintype (Position r)] [∀ r, DecidableEq (Position r)]
    (counts : R → List ℕ)
    (hsize : ∀ r, (counts r).sum = Fintype.card (Position r)) :
    Nat.card
        (∀ r, PrescribedSplits (Finset.univ : Finset (Position r)) (counts r)) =
      ∏ r, Nat.multinomial Finset.univ
        (fun i : Fin (counts r).length => (counts r).get i) := by
  classical
  letI (r : R) := Fintype.ofFinite
    (PrescribedSplits (Finset.univ : Finset (Position r)) (counts r))
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro r hr
  rw [← Nat.card_eq_fintype_card]
  rw [card_prescribedSplits (Finset.univ : Finset (Position r)) (counts r) (by
    simpa using hsize r)]
  exact orderedMultinomial_eq_multinomial (counts r)
