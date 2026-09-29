-- Prove2me | Theorems.Thm_Chou_isFinitelyPresented_of_isFinitelyPresented_of_finite_quotient
-- name    : Chou.isFinitelyPresented_of_isFinitelyPresented_of_finite_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:59:08.816187+00:00
-- url     : https://prove2.me/theorems/ab01cf31-f47f-406b-ad3f-ce1da5a63191
-- title:
--   An extension of a finitely presented group by a finite group is finitely presented
-- statement:
--   If $N$ is a normal subgroup of $G$ such that $N$ is finitely presented and the quotient $G/N$ is
--   finite, then $G$ is finitely presented.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 400 (proof of Lemma 3.1)

import Mathlib

namespace Chou

/-- p. 400, as Chou states it: an extension of a finitely presented group by a finite group is
finitely presented. -/
theorem isFinitelyPresented_of_isFinitelyPresented_of_finite_quotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsFinitelyPresented N] [Finite (G ⧸ N)] : Group.IsFinitelyPresented G := by
  sorry

end Chou
