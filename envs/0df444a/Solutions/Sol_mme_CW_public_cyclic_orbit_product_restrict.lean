-- Prove2me | solution 1 for mme_CW_public_cyclic_orbit_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:28:37.993917+00:00
-- url     : https://prove2.me/submissions/9a49a398-ff9e-427a-8a11-e57fa9bab50d

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation
import Mathlib.Tactic

open MME

universe u

private theorem restrict_kron
    {K : Type u} [Field K] {X X' Y Y' : TensorObj K 3}
    (hX : TensorObj.Restrict X X') (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K 3 (by norm_num)
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hxl := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hyl := P.mul_right _ _ hy (TensorQ.toQ X')
  have hmul : P.le (TensorQ.toQ X * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by
    exact P.le_trans _ _ _ hxl (by simpa [mul_comm] using hyl)
  exact hmul

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {B112 B211 B121 : TensorObj K 3}
    (h112 : TensorObj.Restrict (coupledObj K q) B112)
    (h211 : TensorObj.Restrict
      (TensorObj.permObj cyclicPerm (coupledObj K q)) B211)
    (h121 : TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)) B121) :
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (coupledObj K q))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))))
      (TensorObj.kron B112 (TensorObj.kron B211 B121)) := by
  exact restrict_kron h112 (restrict_kron h211 h121)
