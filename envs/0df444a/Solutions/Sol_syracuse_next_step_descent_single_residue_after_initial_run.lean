-- Prove2me | solution 1 for syracuse_next_step_descent_single_residue_after_initial_run
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T12:10:23.05338+00:00
-- url     : https://prove2.me/submissions/5a269a20-bbef-4471-b662-e9f091d9cdfb

import Theorems.Thm_syracuse_relative_descent_iff_dyadic_divisibility
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

open Nat

/- Solve a*q+d ≡ 3 (mod p). Multiplication by a permutes the residues. -/
private theorem residue (a d p : ℕ) (hp : 0 < p) (hd : d ≤ p)
    (hcop : a.Coprime p) :
    ∃ r < p, ∀ q : ℕ, (a*q+d ≡ 3 [MOD p]) ↔ q%p = r := by
  let z := Nat.chineseRemainder hcop 0 (3+p-d)
  obtain ⟨u, hu⟩ := Nat.modEq_zero_iff_dvd.mp z.property.1
  have h : a*u ≡ 3+p-d [MOD p] := hu ▸ z.property.2
  have target : a*u+d ≡ 3 [MOD p] := by
    have v := h.add_right d
    rw [Nat.sub_add_cancel (by omega)] at v
    exact v.trans (Nat.add_modEq_right : 3+p ≡ 3 [MOD p])
  refine ⟨u%p, Nat.mod_lt _ hp, ?_⟩
  intro q
  constructor
  · intro v
    have hmul : a*q ≡ a*u [MOD p] := (v.trans target.symm).add_right_cancel' d
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm hmul
  · intro v
    exact (((show q ≡ u [MOD p] from v).mul_left a).add_right d).trans target

/- If d*y = a*q-1, the numerators of the next odd step satisfy the affine
   identity d*(3*y+1)+3 = 3*a*q+d. The strict slope gap absorbs the offsets. -/
private theorem band (m a d l h q y : ℕ) (hd2 : 2 ≤ d) (hl : 0 < l)
    (hs : m*d < a) (hlo : l*d*m ≤ 3*a) (hhi : 3*a < h*d*m)
    (hq : h*d+d+3 ≤ q) (hm : 0 < m) (hy : d*y+1=a*q) :
    m*q-1 < y ∧ l*(m*q-1) ≤ 3*y+1 ∧ 3*y+1 < h*(m*q-1) := by
  have hqp : 0 < q := by omega
  have hmqp : 0 < m*q := Nat.mul_pos hm hqp
  have endpoint : d*(m*q) < d*y+1 := by
    rw [hy, show d*(m*q) = (m*d)*q by ring]
    exact Nat.mul_lt_mul_of_pos_right hs hqp
  have above : m*q ≤ y := by
    apply Nat.le_of_mul_le_mul_left (show d*(m*q) ≤ d*y by omega) (by omega : 0 < d)
  have aff : d*(3*y+1)+3 = (3*a)*q+d := by
    calc
      d*(3*y+1)+3 = 3*(d*y+1)+d := by ring
      _ = _ := by rw [hy]; ring
  have adj (v : ℕ) : d*(v*(m*q-1))+v*d = (v*d*m)*q := by
    calc
      d*(v*(m*q-1))+v*d = (v*d)*((m*q-1)+1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hmqp]; ring
  have low := Nat.mul_le_mul_right q hlo
  have high := Nat.mul_le_mul_right q (show 3*a+1 ≤ h*d*m by omega)
  rw [Nat.add_mul, one_mul] at high
  have dl : d ≤ l*d := Nat.le_mul_of_pos_left d hl
  have el := adj l
  have eh := adj h
  refine ⟨by omega, ?_, ?_⟩
  · apply Nat.le_of_mul_le_mul_left (show d*(l*(m*q-1)) ≤ d*(3*y+1) by omega) (by omega : 0 < d)
  · exact Nat.lt_of_mul_lt_mul_left (show d*(3*y+1) < d*(h*(m*q-1)) by omega)

private theorem class_test (k s b q : ℕ) (hs : 0 < s)
    (hup : 2^(k+s) < (3:ℕ)^k)
    (hlo : 2^(k+s+b) ≤ (3:ℕ)^(k+1))
    (hhi : (3:ℕ)^(k+1) < 2^(k+s+b+1))
    (hq : 2^(s+b+1)+2^s+3 ≤ q) :
    let z := 3^k*q-1
    let y := ordCompl[2] z
    (2^s*y = z ∧ 2^k*q-1 < y ∧ syracuseStep y < 2^k*q-1) ↔
      2^(s+b+1) ∣ 3*z+2^s := by
  dsimp only
  let z := 3^k*q-1
  let y := ordCompl[2] z
  let D := 2^s
  let H := 2^(b+1)
  have hd : 0 < D := Nat.two_pow_pos s
  have hd2 : 2 ≤ D := Nat.one_lt_pow (by omega) (by decide)
  have hp : 2^(s+b+1) = D*H := by rw [show s+b+1=s+(b+1) by omega, pow_add]
  have hqpos : 0 < q := by omega
  have hzpos := Nat.mul_pos (pow_pos (by decide : 0 < (3:ℕ)) k) hqpos
  have ez : z+1=3^k*q := Nat.sub_add_cancel hzpos
  have test (hy : D*y=z) : 2^k*q-1 < y ∧
      (syracuseStep y < 2^k*q-1 ↔ H ∣ 3*y+1) := by
    obtain ⟨up, low, high⟩ := band (2^k) (3^k) D (2^b) H q y hd2 (Nat.two_pow_pos b)
      (by simpa only [D, pow_add] using hup)
      (by simpa only [D, pow_add, pow_succ' (3:ℕ), Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlo)
      (by simpa only [D, H, pow_add, pow_succ' (3:ℕ), pow_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi)
      (by simpa only [hp, Nat.mul_comm] using hq)
      (Nat.two_pow_pos _) (by rw [hy, ez])
    exact ⟨up, syracuse_relative_descent_iff_dyadic_divisibility y (2^k*q-1) b low high⟩
  change (D*y=z ∧ 2^k*q-1 < y ∧ syracuseStep y < 2^k*q-1) ↔ 2^(s+b+1) ∣ 3*z+D
  rw [hp]
  have scaled (v : ℕ) (hv : D*v=z) : 3*z+D = D*(3*v+1) := by rw [← hv]; ring
  constructor
  · rintro ⟨hy, _, fall⟩
    rw [scaled y hy]
    exact Nat.mul_dvd_mul_left D ((test hy).2.mp fall)
  · rintro ⟨w, hw⟩
    have hsum : D ∣ 3*z+D := ⟨H*w, by rw [hw]; ring⟩
    have hprod : D ∣ 3*z := (Nat.dvd_add_left (dvd_refl D)).mp hsum
    have co : D.Coprime 3 := (by decide : Nat.Coprime 2 3).pow_left s
    obtain ⟨v, hv⟩ := co.dvd_of_dvd_mul_left hprod
    have em : 3*v+1 = H*w := by
      apply Nat.eq_of_mul_eq_mul_left hd
      simpa only [scaled v hv.symm, Nat.mul_assoc] using hw
    have he : 2 ∣ H := dvd_pow_self 2 (by omega : b+1≠0)
    have he' : 2 ∣ 3*v+1 := em ▸ dvd_mul_of_dvd_left he w
    have ho : ¬2 ∣ v := by omega
    have ey : y=v := by
      dsimp [y]
      rw [hv, Nat.ordCompl_pow_mul_of_not_dvd s Nat.prime_two ho]
    have hy : D*y=z := by rw [ey]; exact hv.symm
    refine ⟨hy, (test hy).1, (test hy).2.mpr ?_⟩
    rw [ey]
    exact ⟨w, em⟩

theorem solution (k s b : ℕ) (hs : 0 < s)
    (hup : 2^(k+s) < (3:ℕ)^k)
    (hlo : 2^(k+s+b) ≤ (3:ℕ)^(k+1))
    (hhi : (3:ℕ)^(k+1) < 2^(k+s+b+1)) :
    ∃ r < 2^(s+b+1),
      (∀ u : ℕ, (3^(k+1)*u+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1) ↔
        u % 2^(s+b+1) = r) ∧ ∀ q : ℕ, 2^(s+b+1)+2^s+3 ≤ q →
      let z := 3^k*q-1
      let y := ordCompl[2] z
      (2^s*y=z ∧ 2^k*q-1 < y ∧ syracuseStep y < 2^k*q-1) ↔
        q % 2^(s+b+1) = r := by
  let p := 2^(s+b+1)
  have co : ((3:ℕ)^(k+1)).Coprime p :=
    ((by decide : Nat.Coprime 3 2).pow_left _).pow_right _
  obtain ⟨r,hr,rule⟩ := residue _ (2^s) p (Nat.two_pow_pos _)
    (Nat.pow_le_pow_right (by decide) (show s ≤ s+b+1 by omega)) co
  refine ⟨r,hr,rule,?_⟩
  intro q hq
  dsimp only
  have cert := class_test k s b q hs hup hlo hhi hq
  dsimp only at cert
  rw [cert, ← rule q]
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (Nat.succ_pos _) hq
  have hpos : 0 < 3^k*q := Nat.mul_pos (pow_pos (by decide : 0 < (3:ℕ)) k) hqpos
  have eqn : 3^(k+1)*q+2^s = 3+(3*(3^k*q-1)+2^s) := by
    rw [pow_succ' (3:ℕ), Nat.mul_assoc]
    omega
  rw [eqn, Nat.add_modEq_left_iff]
