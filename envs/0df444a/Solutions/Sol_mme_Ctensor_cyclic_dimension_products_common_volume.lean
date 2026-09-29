-- Prove2me | solution 1 for mme_Ctensor_cyclic_dimension_products_common_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:25:06.274737+00:00
-- url     : https://prove2.me/submissions/8b4b116c-27ed-4437-be44-7868ed28a04c

import Definitions.Def_CTensorOneHOneCertificate

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume R : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (x y z : Fin R → Fin H) :
    let a := ∏ r, cert.m (x r) * cert.p (y r) * cert.n (z r)
    let b := ∏ r, cert.n (x r) * cert.m (y r) * cert.p (z r)
    let c := ∏ r, cert.p (x r) * cert.n (y r) * cert.m (z r)
    a * b * c = volume ^ (3 * R) := by
  dsimp only
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ r : Fin R,
        (cert.m (x r) * cert.p (y r) * cert.n (z r)) *
          (cert.n (x r) * cert.m (y r) * cert.p (z r)) *
          (cert.p (x r) * cert.n (y r) * cert.m (z r))) =
      ∏ r : Fin R,
        (cert.m (x r) * cert.n (x r) * cert.p (x r)) *
          (cert.m (y r) * cert.n (y r) * cert.p (y r)) *
          (cert.m (z r) * cert.n (z r) * cert.p (z r)) := by
            apply Finset.prod_congr rfl
            intro r _
            ring
    _ = ∏ _r : Fin R, volume * volume * volume := by
          apply Finset.prod_congr rfl
          intro r _
          rw [cert.common_volume (x r), cert.common_volume (y r),
            cert.common_volume (z r)]
    _ = volume ^ (3 * R) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [show volume * volume * volume = volume ^ 3 by ring]
          rw [pow_mul]
