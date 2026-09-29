-- Prove2me | solution 1 for mme_dwz_claim_compatible_iff_retained_fine_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:14:53.300837+00:00
-- url     : https://prove2.me/submissions/45d48f19-fe1c-41e0-8b1f-cd6a8f7c76b2

import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_retained_fine_compatibility

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Copy : Type v} {Position : Type u} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    {owner : Copy}
    (small : MME.DWZTable2StandardForm.UsefulBlock m (outer owner))
    (smallWord : Position → Fin 3 × Fin 3)
    (hSmallWord : smallWord = small.1)
    (j : Copy) :
    (let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (region : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position //
            regionOfShape (outer j t) = region ∧ (smallWord t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m region a) ↔
      retainedFineCompatible m outer
        (fun t ↦ fineSplitGrade (small.1 t).1 (small.1 t).2) j := by
  subst smallWord
  simp only [retainedFineCompatible, fineSplitLeft_encode]
