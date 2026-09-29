-- Prove2me | solution 1 for isSMulRegular_iff_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/dddae1a1-4fa7-5c77-be12-f53eb0bbf3b2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isSMulRegular_iff_of_free

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {r : R} :
    IsSMulRegular M r ↔ IsSMulRegular R r := by
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  constructor
  · intro H m n h
    have i : I := Nonempty.some inferInstance
    have := @H (m • b i) (n • b i) (by simp_all [← mul_smul])
    simpa using congr(b.repr $this i)
  · intro H m n h
    apply b.repr.injective
    ext i
    replace h := congr(b.repr $h i)
    simp only [map_smul] at h
    exact H h

end S_isSMulRegular_iff_of_free
end P2MW
export P2MW.S_isSMulRegular_iff_of_free (solution)
