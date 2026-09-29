-- Prove2me | solution 1 for mme_CW_q6_coupled_survivor_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:36:20.1794+00:00
-- url     : https://prove2.me/submissions/a6db1e3f-58c2-4190-9e87-932af2f81421

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_coupled_cyclic_high_MM_restrict
import Theorems.Thm_mme_CW_coupled_cyclic_low_MM_restrict
import Theorems.Thm_mme_restrict_kronPow

open MME

universe u

namespace CWQ6SurvivorMMRestrict

/-- A square matrix-multiplication tensor remains square under a Kronecker
power, and its side length is raised to the same power. -/
theorem square_kronPow_iso
    {K : Type u} [Field K] (n N : ℕ) :
    TensorObj.Isomorphic
      ((MMObj K n n n).kronPow N)
      (MMObj K (n ^ N) (n ^ N) (n ^ N)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kronPow]
  change (MMq K n n n) ^ N = MMq K (n ^ N) (n ^ N) (n ^ N)
  induction N with
  | zero =>
      simpa using (MMq_one (K := K)).symm
  | succ N ih =>
      rw [pow_succ, ih, MMq_mul]
      simp only [pow_succ]

/-- Restriction is functorial under a Kronecker product in both factors. -/
theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hd : 1 < d)
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict
      (TensorObj.kron X Y)
      (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy (TensorQ.toQ X')
  have hmul : P.le
      (TensorQ.toQ X * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by
    exact P.le_trans _ _ _ hleft (by simpa [mul_comm] using hright)
  exact hmul

theorem survivor_restrict_product_form
    {K : Type u} [Field K] (L G : ℕ) :
    TensorObj.Restrict
      (MMObj K
        ((6 * 6) ^ (2 * G) * 6 ^ (2 * L))
        ((6 * 6) ^ (2 * G) * 6 ^ (2 * L))
        ((6 * 6) ^ (2 * G) * 6 ^ (2 * L)))
      (coupledQ6Survivor K L G) := by
  have hhighPow := mme_restrict_kronPow
    (mme_CW_coupled_cyclic_high_MM_restrict (K := K) 6) (2 * G)
  have hlowPow := mme_restrict_kronPow
    (mme_CW_coupled_cyclic_low_MM_restrict (K := K) 6) (2 * L)
  have hhigh : TensorObj.Restrict
      (MMObj K
        ((6 * 6) ^ (2 * G))
        ((6 * 6) ^ (2 * G))
        ((6 * 6) ^ (2 * G)))
      ((cyclicSymmetrization (MMObj K 6 1 6)).kronPow (2 * G)) :=
    TensorObj.Restrict.trans
      (square_kronPow_iso (K := K) (6 * 6) (2 * G)).2
      hhighPow
  have hlow : TensorObj.Restrict
      (MMObj K
        (6 ^ (2 * L))
        (6 ^ (2 * L))
        (6 ^ (2 * L)))
      ((cyclicSymmetrization (MMObj K 1 6 1)).kronPow (2 * L)) :=
    TensorObj.Restrict.trans
      (square_kronPow_iso (K := K) 6 (2 * L)).2
      hlowPow
  have hblocks := kron_restrict (K := K) (d := 3) (by norm_num) hhigh hlow
  have hcollapse :=
    (MMObj_kron_iso (K := K)
      ((6 * 6) ^ (2 * G)) ((6 * 6) ^ (2 * G)) ((6 * 6) ^ (2 * G))
      (6 ^ (2 * L)) (6 ^ (2 * L)) (6 ^ (2 * L))).2
  exact TensorObj.Restrict.trans hcollapse (by
    simpa only [coupledQ6Survivor] using hblocks)

theorem survivor_side_length (L G : ℕ) :
    (6 * 6) ^ (2 * G) * 6 ^ (2 * L) =
      6 ^ (4 * G + 2 * L) := by
  calc
    (6 * 6) ^ (2 * G) * 6 ^ (2 * L)
        = (6 ^ (2 * G) * 6 ^ (2 * G)) * 6 ^ (2 * L) := by
            rw [mul_pow]
    _ = 6 ^ ((2 * G) + (2 * G)) * 6 ^ (2 * L) := by
          rw [pow_add]
    _ = 6 ^ ((2 * G) + (2 * G) + (2 * L)) := by
          rw [← pow_add]
    _ = 6 ^ (4 * G + 2 * L) := by
          congr 1
          omega

end CWQ6SurvivorMMRestrict

theorem solution
    {K : Type u} [Field K] (L G : ℕ) :
    TensorObj.Restrict
      (MMObj K
        (6 ^ (4 * G + 2 * L))
        (6 ^ (4 * G + 2 * L))
        (6 ^ (4 * G + 2 * L)))
      (coupledQ6Survivor K L G) := by
  simpa only [CWQ6SurvivorMMRestrict.survivor_side_length] using
    CWQ6SurvivorMMRestrict.survivor_restrict_product_form (K := K) L G
