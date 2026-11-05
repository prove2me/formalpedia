-- Prove2me | Theorems.Thm_BrionAntiAffine_proposition_2_5
-- name    : BrionAntiAffine.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:59.191735+00:00
-- url     : https://prove2.me/theorems/753dc799-510f-4b7b-8837-177f67488191
-- title:
--   Proposition 2.5 — the fibre product criterion
-- statement:
--   Let $k$ have characteristic $0$ and $A$ an abelian variety. Let $S$ be an extension of $A$ by a torus $T$ and $W$ an extension of $A$ by a vector group $U$, and let
--
--   $$G=S\times_A W$$
--
--   with its group law, so that $S=G/U$ and $W=G/T$. Then $G$ is anti-affine if and only if $S$ and $W$ are both anti-affine.
--
--   This reduces the characteristic $0$ classification to Propositions 2.1 and 2.3.
--
--   **Formalization Note** $G$ is any group scheme with homomorphisms to $S$ and $W$ making the square cartesian, which pins the group law. Anti-affineness of $G$ is not assumed.
--
--   Differences from the source:
--   - reading: "With the preceding notation": G as in §2.3, which starts from an anti-affine G → G = S ×_A W, for S a torus extension and W a vector extension of A, in characteristic 0, with no anti-affineness assumed; reason: the printed reading would empty the converse, and the printed proof treats G as the fibre product of (2.6)
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Proposition 2.5, p.9, with (2.6)

import Mathlib
import Definitions.Def_BrionAntiAffine_IsTorus
import Definitions.Def_BrionAntiAffine_IsVectorGroup

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Proposition 2.5, Brion, arXiv:0710.5211v3, p.9. With the notation of (2.6): `G` is anti-affine iff
`G/U` and `G/T` are both anti-affine.

**Formalization Note.** Read for the fibre product `G = S ×_A W` of an extension `S` of `A` by a torus
and an extension `W` of `A` by a vector group, in characteristic `0`, with no anti-affineness of `G`
assumed; `S`, `W` play the roles of `G/U`, `G/T`. The surrounding text starts from an anti-affine `G`,
which would empty the converse, and the printed proof treats `G` as this fibre product. The group law
on `G` is pinned by the projections being homomorphisms. -/
theorem proposition_2_5 [CharZero k] (A : Sch k) [GrpObj A] (hA : IsAbelianVariety A)
    (T U S W G : Sch k) [GrpObj T] [GrpObj U] [GrpObj S] [GrpObj W] [GrpObj G]
    (iT : T ⟶ S) (iU : U ⟶ W) (αS : S ⟶ A) (αW : W ⟶ A) (pU : G ⟶ S) (pT : G ⟶ W)
    (hT : IsTorus T) (hU : IsVectorGroup U) (hS : IsExactSeq iT αS) (hW : IsExactSeq iU αW)
    (hpU : IsMonHom pU) (hpT : IsMonHom pT) (hG : IsPullback pU pT αS αW) :
    IsAntiAffine G ↔ IsAntiAffine S ∧ IsAntiAffine W := by sorry

end BrionAntiAffine
