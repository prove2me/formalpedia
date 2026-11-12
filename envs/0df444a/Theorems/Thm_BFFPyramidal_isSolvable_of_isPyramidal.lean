-- Prove2me | Theorems.Thm_BFFPyramidal_isSolvable_of_isPyramidal
-- name    : BFFPyramidal.isSolvable_of_isPyramidal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:30:15.593346+00:00
-- url     : https://prove2.me/theorems/8611ae8b-b20c-449c-992c-5e71742beb66
-- title:
--   Pyramidal groups are solvable
-- statement:
--   Every pyramidal group is solvable.
--
--   Indeed, in the defining chain each step has index equal to the least prime factor of the order of the preceding term, and a subgroup of least prime index is normal; so the chain is a composition series with cyclic factors of prime order, whence the group is solvable. This is why the class of pyramidal groups sits between the supersolvable groups (all of which are pyramidal) and the solvable groups.
--
--   **Formalization note.** Solvability is Mathlib's `Group.IsSolvable`. The trivial group is included and is solvable.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 139, the remark following eq. (2) (citing Rotman, The Theory of Groups, Exer. 3.43)

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal

namespace BFFPyramidal

theorem isSolvable_of_isPyramidal {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G) :
    Group.IsSolvable G := by
  sorry

end BFFPyramidal
