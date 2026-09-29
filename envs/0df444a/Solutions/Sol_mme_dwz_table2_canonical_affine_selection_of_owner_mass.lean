-- Prove2me | solution 1 for mme_dwz_table2_canonical_affine_selection_of_owner_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T00:07:04.104763+00:00
-- url     : https://prove2.me/submissions/edba9697-9ec1-41a4-bc88-0fb4293a9e46

import Theorems.Thm_mme_dwz_table2_canonical_affine_weighted_aggregate_selection

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

/-!
# Weighted affine selection from uniform ownerwise mass

This theorem is the finite double-counting seam between ownerwise Claim-6.8
mass and the canonical first-hash selector.  It is deliberately independent
of the tensor maps and of the concrete definition of the owner mass.
-/

theorem solution
    {p N : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d cap : ℕ) (hcap : 0 < cap) (hmod : 8 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeX (b t)) =
          (fun t ↦ DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeY (b t)) =
          (fun t ↦ DWZSquare.shapeY (a t)))).card ≤ d)
    (mass : ((Fin (N + 2) → ZMod p) × ZMod p) →
      (Fin (N + 1) → Fin 15) → ℕ)
    (hmassCap : ∀ q a, a ∈ T →
      a ∈ dwzTable2AffineHashBucket S A q → mass q a ≤ cap)
    (howner : ∀ a ∈ T,
      7 * S.card * p ^ (N + 1) * cap ≤
        8 * ∑ q ∈ (Finset.univ.filter (fun q :
            (Fin (N + 2) → ZMod p) × ZMod p ↦
          a ∈ dwzTable2AffineHashBucket S A q)),
          mass q a) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
      ∃ I : Finset (Fin (N + 1) → Fin 15),
        I ⊆ T ∧
        I ⊆ dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I, ∀ e' ∈ dwzTable2AffineHashBucket S A q,
          (fun t ↦ DWZSquare.shapeX (e t)) =
              (fun t ↦ DWZSquare.shapeX (e' t)) ∨
            (fun t ↦ DWZSquare.shapeY (e t)) =
              (fun t ↦ DWZSquare.shapeY (e' t)) → e = e') ∧
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ a ∈ I, (mass q a : ℝ) / (cap : ℝ) := by
  classical
  let State := (Fin (N + 2) → ZMod p) × ZMod p
  let bucket : State → Finset (Fin (N + 1) → Fin 15) := fun q ↦
    dwzTable2AffineHashBucket S A q
  let ownerMass (a : Fin (N + 1) → Fin 15) : ℕ :=
    ∑ q ∈ (Finset.univ.filter (fun q : State ↦ a ∈ bucket q)), mass q a
  let total : ℕ :=
    ∑ q : State, ∑ a ∈ T.filter (fun a ↦ a ∈ bucket q), mass q a
  have hswap : (∑ a ∈ T, ownerMass a) = total := by
    dsimp only [ownerMass, total]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  have hsumNat :
      T.card * (7 * S.card * p ^ (N + 1) * cap) ≤ 8 * total := by
    calc
      T.card * (7 * S.card * p ^ (N + 1) * cap) =
          ∑ _a ∈ T, 7 * S.card * p ^ (N + 1) * cap := by
        simp
      _ ≤ ∑ a ∈ T, 8 * ownerMass a :=
        Finset.sum_le_sum fun a ha ↦ howner a ha
      _ = 8 * ∑ a ∈ T, ownerMass a := by
        rw [Finset.mul_sum]
      _ = 8 * total := by rw [hswap]
  have hsumReal :
      (7 / 8 : ℝ) *
          ((cap : ℝ) * (T.card : ℝ) * (S.card : ℝ) *
            (p : ℝ) ^ (N + 1)) ≤
        (total : ℝ) := by
    have hcast : ((T.card *
        (7 * S.card * p ^ (N + 1) * cap) : ℕ) : ℝ) ≤
        ((8 * total : ℕ) : ℝ) := by exact_mod_cast hsumNat
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
    nlinarith
  have htotalCast :
      (total : ℝ) =
        ∑ q : State,
          (((∑ a ∈ T.filter (fun a ↦ a ∈ bucket q), mass q a) : ℕ) : ℝ) := by
    dsimp only [total]
    norm_num only [Nat.cast_sum]
  have hmassTotal :
      (7 / 8 : ℝ) *
          ((cap : ℝ) * (T.card : ℝ) * (S.card : ℝ) *
            (p : ℝ) ^ (N + 1)) ≤
        ∑ q : State,
          (((∑ a ∈ T.filter (fun a ↦
            a ∈ dwzTable2AffineHashBucket S A q), mass q a) : ℕ) : ℝ) := by
    rw [← htotalCast]
    simpa only [State, bucket] using hsumReal
  exact mme_dwz_table2_canonical_affine_weighted_aggregate_selection
    hpodd hp5 S hSrange hSfree A T hTA d cap hcap hmod hx hy mass
    hmassCap hmassTotal
