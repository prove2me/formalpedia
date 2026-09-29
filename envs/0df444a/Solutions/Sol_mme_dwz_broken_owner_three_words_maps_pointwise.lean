-- Prove2me | solution 1 for mme_dwz_broken_owner_three_words_maps_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:00:52.737832+00:00
-- url     : https://prove2.me/submissions/e1f10a19-d7c5-4158-8f55-9f60ef07147d

import Definitions.Def_mme_dwz_broken_owner_three_words_data

open MME Module
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (i : Fin 3) :
    brokenOwnerThreeWordsWordMap K m outer copy x y z i =
      brokenOwnerThreeWordsSelectedMap K m outer copy x y z i := by
  fin_cases i <;> rfl
