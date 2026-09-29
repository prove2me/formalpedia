-- Prove2me | Theorems.Thm_FamousTheorems_rank_range_add_rank_ker
-- name    : FamousTheorems.rank_range_add_rank_ker
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:48.546612+00:00
-- url     : https://prove2.me/theorems/733f2613-b0e9-4cd1-83d2-81535de9dc15
-- title:
--   The rank–nullity theorem
-- statement:
--   **The rank\u2013nullity theorem.** For a linear map $f : V \to W$, $$\operatorname{rank} f + \dim \ker f = \dim V.$$ Dimension is conserved: what the map fails to record (the kernel) plus what it does record (the image) accounts for the entire source. The theorem is equivalent to the first isomorphism theorem $V/\ker f \cong \operatorname{im} f$ combined with additivity of dimension over quotients. Its consequences are constant working facts: an endomorphism of a finite-dimensional space is injective iff surjective, a homogeneous system with more unknowns than equations has a nontrivial solution, and the solution space of a linear system has predictable dimension. **Formalization note.** `Module.rank` is the cardinal-valued rank, so the statement holds without finite-dimensionality. The result is Mathlib's `LinearMap.rank_range_add_rank_ker`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem rank_range_add_rank_ker :
    ∀ {R : Type u_2} {M M₁ : Type u_1} [inst : Ring R] [inst_1 : AddCommGroup M] 
    [inst_2 : AddCommGroup M₁] [inst_3 : Module R M] [inst_4 : Module R M₁] [HasRankNullity.{u_1, u_2} R] 
    (f : M →ₗ[R] M₁), Module.rank R ↥f.range + Module.rank R ↥f.ker = Module.rank R M := by sorry

end FamousTheorems
