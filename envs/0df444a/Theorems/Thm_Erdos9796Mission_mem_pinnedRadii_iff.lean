-- Prove2me | Theorems.Thm_Erdos9796Mission_mem_pinnedRadii_iff
-- name    : Erdos9796Mission.mem_pinnedRadii_iff
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-11T16:27:26.635354+00:00
-- url     : https://prove2.me/theorems/10eda7dc-19b1-4215-8645-ff67ee885f1f
-- title:
--   Characterize the realized positive radii
-- statement:
--   A real number r is among the positive radii realized from p in A exactly when r is positive and some point q of A has distance r from p.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/3d0e9306396f0aa6639f4453174693990fe9c242/lean/Erdos9796Proof/P97/PinnedMultiplicity.lean#L168-L171

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity

theorem Erdos9796Mission.mem_pinnedRadii_iff
    {A : Finset Erdos9796Mission.Plane} {p : Erdos9796Mission.Plane} {r : ℝ} :
    r ∈ Erdos9796Mission.pinnedRadii A p ↔
      (∃ q ∈ A, dist p q = r) ∧ 0 < r := by sorry
