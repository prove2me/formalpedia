-- Prove2me | solution 1 for mme_schonhage_pan_degenerates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T03:42:10.19164+00:00
-- url     : https://prove2.me/submissions/733fe530-ffbe-4c83-8db2-544c78da3ff1

import Theorems.Thm_mme_schonhage_pan_degenerates_of_order_twelve

open MME

universe u

theorem solution {K : Type u} [Field K] :
    Degenerates
      (TensorObj.bigAdd ![
        MMObj K 1 5 22,
        MMObj K 11 2 5,
        MMObj K 10 11 1])
      (TensorObj.diagObj K 3 156) := by
  exact ⟨12, mme_schonhage_pan_degenerates_of_order_twelve⟩
