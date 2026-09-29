-- Prove2me | Theorems.Thm_BrinSquier_abelian_subgroup_of_free_isCyclic
-- name    : BrinSquier.abelian_subgroup_of_free_isCyclic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:19:02.644282+00:00
-- url     : https://prove2.me/theorems/a6093890-209b-4edf-8ac0-96e65893642c
-- title:
--   An abelian subgroup of a free group is cyclic
-- statement:
--   If $G$ is a free group and $H \le G$ is abelian, then $H$ is cyclic.
--
--    The trivial subgroup counts as cyclic, so no nontriviality is claimed.
-- source:
--   Standard consequence of the Nielsen-Schreier theorem. Substituted for Corollary (3.3) of M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, which finishes through metabelian-or-free-abelian-of-infinite-rank; this mission takes the free-group route instead.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem abelian_subgroup_of_free_isCyclic {G : Type*} [Group G] [IsFreeGroup G]
    (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : IsCyclic H := by
  sorry

end BrinSquier
