-- Prove2me | solution 1 for gpy_card_filter_tupleSupport_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:27:22.132803+00:00
-- url     : https://prove2.me/submissions/dcbafa79-3be3-4357-931a-7e5dbd78887b

/- Submission file for the Prove2Me problem `gpy_card_filter_tupleSupport_prod_le` (publish2 fiber batch).
   Self-contained: imports Mathlib only. Contains the verified helper
   bodies needed for the proof, with top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

/-- The support set for tuple Selberg weights at level R: tuples of positive
    integers, each at most R, whose product is at most R. -/
def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)

/-- Membership in the support set, unfolded. -/
theorem mem_tupleSupport {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩

/-- Number of ordered factorizations of `D` into `k` positive factors:
    the `k`-fold divisor function `τ_k(D)` in the form the sums need.
    (Each factor is at most `D` automatically when the product is `D`
    and all factors are positive, so `Icc 1 D` is the right range.) -/
def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card

/-- The fiber of the support over a product `D` has card at most
    `τ_k(D)`: a support tuple with product `D` has all entries
    between `1` and `D`, hence is a `k`-factorization of `D`. -/
theorem card_filter_tupleSupport_prod_le {k R D : ℕ} :
    ((tupleSupport k R).filter (fun d => ∏ i, d i = D)).card
      ≤ tupleProdCount k D := by
  apply Finset.card_le_card
  intro d hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hdmem, hprod⟩ := hd
  obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hdmem
  rw [Finset.mem_filter]
  refine ⟨?_, hprod⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  refine ⟨h1 i, ?_⟩
  have hle : d i ≤ ∏ j, d j :=
    Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
  rw [hprod] at hle
  exact hle

theorem card_filter_tupleSupport_prod_le_restated_pub2 {k R D : ℕ} :
    (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter (fun d => ∏ i, d i = D)).card
      ≤ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D)).card := by
  have hmain := card_filter_tupleSupport_prod_le (k := k) (R := R) (D := D)
  unfold tupleSupport tupleProdCount at hmain
  exact hmain


end GPY

theorem solution {k R D : ℕ} :
    (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter (fun d => ∏ i, d i = D)).card
      ≤ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D)).card := GPY.card_filter_tupleSupport_prod_le_restated_pub2
