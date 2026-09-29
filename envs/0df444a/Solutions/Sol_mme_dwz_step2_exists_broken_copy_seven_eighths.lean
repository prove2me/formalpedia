-- Prove2me | solution 1 for mme_dwz_step2_exists_broken_copy_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:45:56.08967+00:00
-- url     : https://prove2.me/submissions/56ec8a74-9b54-4280-9b21-82032a41f357

import Theorems.Thm_mme_dwz_claim6_8_exists_seven_eighths_nonholes
import Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block Outer Weight : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Outer] [DecidableEq Outer]
    [Fintype Weight] [DecidableEq Weight] [Nonempty Weight]
    (compatible useful : Block → Outer → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hashRetained : Outer → Weight → Prop)
    [DecidableRel hashRetained]
    (retained : Outer)
    (hUseful : ∀ z : Block, useful z retained)
    (hCompatible : ∀ z : Block, compatible z retained)
    (hHash : ∀ w : Weight, hashRetained retained w)
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (fun w : Weight ↦
        1 < (Finset.univ.filter (fun A : Outer ↦
          compatible z A ∧ hashRetained A w)).card)).card ≤
        Fintype.card Weight) :
    ∃ w : Weight,
      7 * Fintype.card Block ≤
        8 * (MME.DWZStep2.brokenCopy
          (fun z A ↦ compatible z A ∧ hashRetained A w)
          useful retained).nonholes.card := by
  classical
  let bad : Block → Weight → Prop := fun z w ↦
    1 < (Finset.univ.filter (fun A : Outer ↦
      compatible z A ∧ hashRetained A w)).card
  obtain ⟨w, hw⟩ :=
    mme_dwz_claim6_8_exists_seven_eighths_nonholes bad hpointwise
  refine ⟨w, ?_⟩
  have hfilter :
      Finset.univ.filter (fun z : Block ↦ ¬ bad z w) =
        (MME.DWZStep2.brokenCopy
          (fun z A ↦ compatible z A ∧ hashRetained A w)
          useful retained).nonholes := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hnotbad
      by_contra hhole
      exact hnotbad
        ((mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
          compatible useful hashRetained z retained w
          (hUseful z) (hCompatible z) (hHash w)).mp hhole)
    · intro hnonhole hbad
      exact
        ((mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
          compatible useful hashRetained z retained w
          (hUseful z) (hCompatible z) (hHash w)).mpr hbad) hnonhole
  simpa only [hfilter] using hw
