-- Prove2me | solution 1 for mme_kronFin_respects_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:34:53.269672+00:00
-- url     : https://prove2.me/submissions/ba272958-29e0-4918-ad2d-57d14220f3c4

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tensor_quotient

open MME

universe u

theorem solution
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (R : ℕ) (X Y : Fin R → TensorObj K d),
      (∀ r, TensorObj.Isomorphic (X r) (Y r)) →
      TensorObj.Isomorphic
        (TensorObj.kronFin R X) (TensorObj.kronFin R Y) := by
  intro R
  induction R with
  | zero =>
      intro X Y h
      exact TensorObj.Isomorphic.refl _
  | succ R ih =>
      intro X Y h
      have hhead : TensorObj.Isomorphic (X 0) (Y 0) := h 0
      have htail : TensorObj.Isomorphic
          (TensorObj.kronFin R (fun r => X r.succ))
          (TensorObj.kronFin R (fun r => Y r.succ)) :=
        ih (fun r => X r.succ) (fun r => Y r.succ) (fun r => h r.succ)
      exact TensorQ.mul_respects_iso hhead htail
