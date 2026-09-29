-- Prove2me | Theorems.Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone
-- name    : AlgebraicGeometry.FGSubalgebra.nonempty_isColimit_cocone
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/800236b8-20b0-556d-a117-e08aa732711c
-- title:
--   An algebra is the filtered colimit of its f.g. subalgebras
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra, both in a fixed universe. Write $\mathrm{FGSubalgebra}\ R\ A$ for the type of pairs consisting of an $R$-subalgebra $A_0 \subseteq A$ together with a proof that $A_0$ is finitely generated, regarded as a category via the order relation inherited from inclusion of subalgebras. The functor [`AlgebraicGeometry.FGSubalgebra.diagram`](def/AlgebraicGeometry_FGSubalgebra.html#L36) into the category of commutative rings sends such an $A_0$ to its underlying commutative ring and sends the unique morphism coming from $A_0 \le A_1$ to the inclusion ring homomorphism $A_0 \hookrightarrow A_1$; the cocone [`AlgebraicGeometry.FGSubalgebra.cocone`](def/AlgebraicGeometry_FGSubalgebra.html#L42) has vertex $A$ and component at $A_0$ the inclusion $A_0 \hookrightarrow A$ (these are compatible with the transition maps). The theorem asserts that the type of colimit structures on this cocone is nonempty, i.e. the inclusions exhibit $A$ as the colimit, in the category of commutative rings, of the diagram of its finitely generated $R$-subalgebras. Since `IsColimit` is data rather than a proposition, the conclusion is phrased as the nonemptiness of that type.
--
--   This is the ring-theoretic statement that every algebra is the filtered colimit of its finitely generated subalgebras, the source of all 'finite presentation commutes with filtered colimits' arguments. It is used to present $\operatorname{Spec} A$ as the limit of the affine schemes $\operatorname{Spec} A_0$ in [`AlgebraicGeometry.FGSubalgebra.nonempty_isLimit_specCone`](thm.html#AlgebraicGeometry.FGSubalgebra.nonempty_isLimit_specCone).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone.lean

import Definitions.Def_AlgebraicGeometry_FGSubalgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.FGSubalgebra.nonempty_isColimit_cocone
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by sorry
