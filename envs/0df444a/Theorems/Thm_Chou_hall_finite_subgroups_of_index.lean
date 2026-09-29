-- Prove2me | Theorems.Thm_Chou_hall_finite_subgroups_of_index
-- name    : Chou.hall_finite_subgroups_of_index
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:58:34.392006+00:00
-- url     : https://prove2.me/theorems/370ae02f-5f56-43b4-b977-b14d5740abde
-- title:
--   M. Hall: a finitely generated group has finitely many subgroups of each index (external)
-- statement:
--   If $G$ is finitely generated then for every $n \ne 0$ there are only finitely many subgroups of
--   $G$ of index $n$. (Mathlib's index $0$ stands for infinite index, which is excluded.)
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 400 (M. Hall, cited via Kurosh vol. 2, p. 56)

import Mathlib

namespace Chou

/-- M. Hall (p. 400, external): a finitely generated group has only finitely many subgroups of
each finite index `n ≠ 0` (Mathlib's index `0` means infinite index). -/
theorem hall_finite_subgroups_of_index {G : Type*} [Group G] [Group.FG G] (n : ℕ) (hn : n ≠ 0) :
    Finite {H : Subgroup G // H.index = n} := by
  sorry

end Chou
