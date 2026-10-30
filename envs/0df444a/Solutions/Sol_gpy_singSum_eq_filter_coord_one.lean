-- Prove2me | solution 1 for gpy_singSum_eq_filter_coord_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:10:36.564997+00:00
-- url     : https://prove2.me/submissions/4797bb9f-ec8b-4efb-874a-df4abb18b93d

/- Submission file for the Prove2Me problem `gpy_singSum_eq_filter_coord_one` (publish2 first-moment batch).
   Self-contained: imports Mathlib only. Top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d => d i = 1),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e => e i = 1),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0) := by
  have hcoord : ∀ (d e : Fin k → ℕ) (i : Fin k),
      (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      d i = 1 ∧ e i = 1 := by
    intro d e i hg
    obtain ⟨w, hw, hcop⟩ := hg
    have hdvd1 : Nat.lcm (d i) (e i) ∣ w + h i := hw i
    have hdvdL : Nat.lcm (d i) (e i)
        ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
      Finset.dvd_lcm (Finset.mem_univ i)
    have hgcd : Nat.lcm (d i) (e i)
        ∣ Nat.gcd (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
      Nat.dvd_gcd hdvd1 hdvdL
    rw [hcop.gcd_eq_one] at hgcd
    have hlcm1 : Nat.lcm (d i) (e i) = 1 := Nat.dvd_one.mp hgcd
    constructor
    · exact Nat.dvd_one.mp (hlcm1 ▸ Nat.dvd_lcm_left (d i) (e i))
    · exact Nat.dvd_one.mp (hlcm1 ▸ Nat.dvd_lcm_right (d i) (e i))
  have hsplit_d : (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0))
      = (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d => d i = 1),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
            (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
              ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
             else 0))
        + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d => ¬ d i = 1),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
              (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
                ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
               else 0)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hzero_d : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d => ¬ d i = 1),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg (fun hg => hd.2 (hcoord d e i hg).1)]
  rw [hsplit_d, hzero_d, add_zero]
  apply Finset.sum_congr rfl
  intro d _
  have hsplit_e : (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0))
      = (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e => e i = 1),
          (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0))
        + (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e => ¬ e i = 1),
            (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
              ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
             else 0)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hzero_e : (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e => ¬ e i = 1),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_filter] at he
    rw [if_neg (fun hg => he.2 (hcoord d e i hg).2)]
  rw [hsplit_e, hzero_e, add_zero]
