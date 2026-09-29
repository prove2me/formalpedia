-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_of_finite_of_isNilpotent_quotient
-- name    : Chou.isVirtuallyNilpotent_of_finite_of_isNilpotent_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:56:52.561024+00:00
-- url     : https://prove2.me/theorems/64d17fb2-b9ec-4636-89b9-7ee04e37504d
-- title:
--   Finite-by-nilpotent groups are almost nilpotent
-- statement:
--   If $N$ is a finite normal subgroup of $G$ and $G/N$ is nilpotent, then $G$ has a nilpotent
--   subgroup of finite index.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 399 (remark before Lemma 3.1)

import Mathlib

namespace Chou

/-- p. 399: a finite-by-nilpotent group is almost nilpotent. -/
theorem isVirtuallyNilpotent_of_finite_of_isNilpotent_quotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Finite N]
    (h : Group.IsNilpotent (G ⧸ N)) : Group.IsVirtuallyNilpotent G := by
  sorry

end Chou
