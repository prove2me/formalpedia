-- Prove2me | solution 1 for mme_Ctensor_three_star_dimension_products_common_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:35:29.247313+00:00
-- url     : https://prove2.me/submissions/fa5af62b-d870-4248-ab80-1c74961e552b

import Definitions.Def_CTensorOneHOneCertificate

open MME BigOperators

universe u

/-!
The common-volume calculation for three distinct C-tensor stars.  This is
the arithmetic point at which source-faithful per-address matrix-product
shapes replace the false fixed-survivor identification.
-/
theorem solution
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume R : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (x y z : Fin R → Fin H) :
    let a := ∏ r, certX.m (x r) * certY.p (y r) * certZ.n (z r)
    let b := ∏ r, certX.n (x r) * certY.m (y r) * certZ.p (z r)
    let c := ∏ r, certX.p (x r) * certY.n (y r) * certZ.m (z r)
    a * b * c = volume ^ (3 * R) := by
  dsimp only
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ r : Fin R,
        (certX.m (x r) * certY.p (y r) * certZ.n (z r)) *
          (certX.n (x r) * certY.m (y r) * certZ.p (z r)) *
          (certX.p (x r) * certY.n (y r) * certZ.m (z r))) =
      ∏ r : Fin R,
        (certX.m (x r) * certX.n (x r) * certX.p (x r)) *
          (certY.m (y r) * certY.n (y r) * certY.p (y r)) *
          (certZ.m (z r) * certZ.n (z r) * certZ.p (z r)) := by
            apply Finset.prod_congr rfl
            intro r _
            ring
    _ = ∏ _r : Fin R, volume * volume * volume := by
          apply Finset.prod_congr rfl
          intro r _
          rw [certX.common_volume (x r), certY.common_volume (y r),
            certZ.common_volume (z r)]
    _ = volume ^ (3 * R) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [show volume * volume * volume = volume ^ 3 by ring]
          rw [pow_mul]
