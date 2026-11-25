-- Prove2me | solution 1 for syracuse_valuation_word_unique_residue_and_affine_progression
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T00:37:33.740855+00:00
-- url     : https://prove2.me/submissions/25eed78f-66cb-4a11-a33c-13d6f9c6aa28

import Theorems.Thm_syracuse_valuation_word_affine_identity
import Theorems.Thm_syracuse_mixed_valuation_prefix_descent_certificate
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

open Nat

private theorem affineResidue (a c p d : ℕ) (hp : 0 < p) (hc : a.Coprime p) :
    ∃ r < p, ∀ x : ℕ, (a*x+c ≡ d [MOD p]) ↔ x%p=r := by
  let t := d+p-c%p
  let z := Nat.chineseRemainder hc 0 t
  obtain ⟨u, hu⟩ := Nat.modEq_zero_iff_dvd.mp z.property.1
  have hz : a*u ≡ t [MOD p] := hu ▸ z.property.2
  have eqn : t+c%p=d+p := Nat.sub_add_cancel
    ((Nat.mod_lt c hp).le.trans (Nat.le_add_left p d))
  have hbase : a*u+c ≡ d [MOD p] := by
    have e := hz.add (Nat.mod_modEq c p).symm
    rw [eqn] at e
    exact e.trans (Nat.add_modEq_right : d+p ≡ d [MOD p])
  refine ⟨u%p, Nat.mod_lt _ hp, ?_⟩
  intro x
  constructor
  · intro hx
    exact Nat.ModEq.cancel_left_of_coprime hc.symm ((hx.trans hbase.symm).add_right_cancel' c)
  · intro hx
    exact (((show x ≡ u [MOD p] from hx).mul_left a).add_right c).trans hbase

theorem solution (w : List ℕ) (hne : w ≠ [])
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a) :
    let P := 2^(w.sum+1)
    ∃ r < P,
      (∀ y : ℕ, y % P = r ↔ List.ofFn (fun i : Fin w.length =>
        (3*syracuseStep^[i.val] y+1).factorization 2) = w) ∧
      (∀ m : ℕ, syracuseStep^[w.length] (r+P*m) =
        syracuseStep^[w.length] r+2*3^w.length*m) := by
  dsimp only
  let D := 2^w.sum
  let P := 2^(w.sum+1)
  let A := 3^w.length
  let C := syracuseAffineConstant w
  have hd : 0 < D := Nat.two_pow_pos _
  have hp : 0 < P := Nat.two_pow_pos _
  have ep : P=2*D := by dsimp [P,D]; rw [pow_succ, Nat.mul_comm]
  have hlt : D < P := by omega
  have co : A.Coprime P := (((by decide : Nat.Coprime 3 2).pow_left _).pow_right _)
  obtain ⟨r,hr,rule⟩ := affineResidue A C P D hp co
  have characterized (y : ℕ) : y%P=r ↔ List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] y+1).factorization 2)=w := by
    rw [← rule y]
    constructor
    · intro hm
      have hrem : (A*y+C)%P=D := Eq.trans hm (Nat.mod_eq_of_lt hlt)
      have hs : A*y+C < D*(A*y+C+1) :=
        lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_left _ hd)
      exact (syracuse_mixed_valuation_prefix_descent_certificate w y (A*y+C+1) hpos hrem hs).2.2
    · intro hw
      let z := syracuseStep^[w.length] y
      have eqn : D*z=A*y+C := syracuse_valuation_word_affine_identity w y hw
      have ho : ¬2 ∣ z := by
        have hwlen : 0 < w.length := List.length_pos_iff.mpr hne
        obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hwlen.ne'
        dsimp [z]
        rw [ht, Function.iterate_succ_apply', syracuseStep]
        exact Nat.not_dvd_ordCompl Nat.prime_two (by omega)
      have zmod : z ≡ 1 [MOD 2] := by change z%2=1%2; omega
      have hm : D*z ≡ D*1 [MOD D*2] := zmod.mul_left' D
      rw [eqn, Nat.mul_one, Nat.mul_comm D 2, ← ep] at hm
      exact hm
  refine ⟨r,hr,characterized,?_⟩
  intro m
  have b := (characterized r).mp (Nat.mod_eq_of_lt hr)
  have x := (characterized (r+P*m)).mp (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr])
  have eb := syracuse_valuation_word_affine_identity w r b
  have ex := syracuse_valuation_word_affine_identity w (r+P*m) x
  apply Nat.eq_of_mul_eq_mul_left hd
  calc
    _ = A*(r+P*m)+C := ex
    _ = (A*r+C)+D*(2*A*m) := by rw [ep]; ring
    _ = _ := by rw [← eb, Nat.mul_add]
