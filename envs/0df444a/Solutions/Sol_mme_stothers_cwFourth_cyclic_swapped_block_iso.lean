-- Prove2me | solution 1 for mme_stothers_cwFourth_cyclic_swapped_block_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:59:31.571273+00:00
-- url     : https://prove2.me/submissions/2678f596-fffa-4f13-a21a-9ccc8984dc63

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_oriented_cyclic_classes
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_cyclicSymmetrization_permObj_swapFirstTwo_iso
import Theorems.Thm_mme_stothers_cwFourth_swapped_block_iso

open MME

universe u

set_option autoImplicit false

namespace CyclicSwappedConstituentIsoReduction

private theorem cyclicSymmetrization_isomorphic
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Isomorphic X Y) :
    TensorObj.Isomorphic
      (cyclicSymmetrization X) (cyclicSymmetrization Y) := by
  apply (TensorQ.toQ_eq_iff).1
  have hq : TensorQ.toQ X = TensorQ.toQ Y :=
    (TensorQ.toQ_eq_iff).2 h
  rw [cyclicSymmetrization_eq_public_perm,
    cyclicSymmetrization_eq_public_perm]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  rw [hq]

end CyclicSwappedConstituentIsoReduction

theorem solution
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    TensorObj.Isomorphic
      (cyclicSymmetrization
        ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
          (MME.StothersFourth.fixedModeRelabel swapFirstTwoPerm ρ)))
      (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization
          ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
            ρ))) := by
  exact
    (CyclicSwappedConstituentIsoReduction.cyclicSymmetrization_isomorphic
      (mme_stothers_cwFourth_swapped_block_iso q ρ)).trans
    (mme_cyclicSymmetrization_permObj_swapFirstTwo_iso
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        ρ))
