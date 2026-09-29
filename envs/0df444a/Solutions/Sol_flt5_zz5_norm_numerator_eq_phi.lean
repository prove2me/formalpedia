-- Prove2me | solution 1 for flt5_zz5_norm_numerator_eq_phi
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T14:56:31.297071+00:00
-- url     : https://prove2.me/submissions/c4784634-891d-466c-95af-dce3df7a2862
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Theorems.Thm_flt5_zz5_galois_prod_ring_id
import Theorems.Thm_flt5_zz5_norm_galois_prod

-- v6 fix: in goal_via_map, replace push_cast;ring with simp[map_pow,map_intCast,...] to
-- normalize algebraMap ℚ CK5 ((a:ℚ)^4-...) to (a:CK5)^4-... matching key's RHS.

noncomputable section

abbrev ZZ5v6 := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5v6 := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5v6 :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5v6 :=
  IsCyclotomicExtension.numberField {5} ℚ CK5v6

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (a b : ℤ) (ζ : ZZ5v6) (hζ : IsPrimitiveRoot (ζ : CK5v6) 5) :
    Algebra.norm ℤ ((a : ZZ5v6) + ζ * (b : ZZ5v6)) =
    a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
  have hring := flt5_zz5_galois_prod_ring_id (ζ : CK5v6) hζ a b
  have hnorm := flt5_zz5_norm_galois_prod a b (ζ : CK5v6) hζ
  -- Step 1: reduce to ℚ equality
  suffices h : (Algebra.norm ℤ ((a : ZZ5v6) + ζ * (b : ZZ5v6)) : ℚ) =
      (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 : ℤ) by exact_mod_cast h
  push_cast
  rw [Algebra.coe_norm_int]
  -- Fix ZZ5v6→CK5v6 coercion (norm_cast handles ↑↑a = ↑a mismatch)
  have hcoerce : (((a : ZZ5v6) + ζ * (b : ZZ5v6) : ZZ5v6) : CK5v6) =
      (a : CK5v6) + (ζ : CK5v6) * b := by
    push_cast [map_add, map_mul]; norm_cast
  rw [hcoerce]
  -- key: norm mapped to CK5v6 via Galois product formula then ring identity
  have key : algebraMap ℚ CK5v6 (Algebra.norm ℚ ((a : CK5v6) + (ζ : CK5v6) * b)) =
      (a : CK5v6) ^ 4 - (a : CK5v6) ^ 3 * b + (a : CK5v6) ^ 2 * (b : CK5v6) ^ 2 -
      (a : CK5v6) * (b : CK5v6) ^ 3 + (b : CK5v6) ^ 4 := by
    rw [hnorm]; exact hring
  -- goal_via_map: use simp[map_*] to normalize algebraMap ℚ CK5v6 applied to ℚ-polynomial
  have goal_via_map :
      algebraMap ℚ CK5v6 (Algebra.norm ℚ ((a : CK5v6) + (ζ : CK5v6) * b)) =
      algebraMap ℚ CK5v6 ((a : ℚ) ^ 4 - (a : ℚ) ^ 3 * b + (a : ℚ) ^ 2 * (b : ℚ) ^ 2 -
        (a : ℚ) * (b : ℚ) ^ 3 + (b : ℚ) ^ 4) := by
    rw [key]
    simp only [map_sub, map_add, map_mul, map_pow, map_intCast]
  exact (algebraMap ℚ CK5v6).injective goal_via_map

end
