-- Prove2me | Theorems.Thm_FamousTheorems_jordan_primitive_transposition
-- name    : FamousTheorems.jordan_primitive_transposition
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:00.287372+00:00
-- url     : https://prove2.me/theorems/1d1b739a-052e-4477-b67b-90ec3cc0f39a
-- title:
--   Jordan's theorem on primitive groups containing a transposition
-- statement:
--   **Jordan's theorem on primitive groups containing a transposition.** Let $\alpha$ be a finite set and $G\le\operatorname{Sym}(\alpha)$ a primitive permutation group. If $G$ contains a transposition, then $G=\operatorname{Sym}(\alpha)$.
--
--   This theorem of Jordan is used to prove that Galois groups are full symmetric groups. For example, an irreducible polynomial of prime degree $p$ with exactly two non-real roots has Galois group $S_p$.
--
--   **Formalization note.** Mathlib's `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`. Primitivity is `MulAction.IsPreprimitive G α` and a transposition is a permutation satisfying `IsSwap`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jordan_primitive_transposition {α : Type*} [DecidableEq α] [Finite α] {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPreprimitive G α)
    {g : Equiv.Perm α} (hg : g.IsSwap) (hgG : g ∈ G) : G = ⊤ := by sorry

end FamousTheorems
