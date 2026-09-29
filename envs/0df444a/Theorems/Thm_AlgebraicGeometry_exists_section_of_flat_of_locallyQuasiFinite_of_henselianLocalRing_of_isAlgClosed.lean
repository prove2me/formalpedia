-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
-- name    : AlgebraicGeometry.exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c5bf88b8-f6cb-5ed3-9ef5-adf856144095
-- title:
--   Sections of flat quasi-finite schemes over henselian valuation rings
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, a valuation ring and a henselian local ring, and let $K$ be an algebraically closed field which is an $R$-algebra and a fraction field of $R$. Let $X$ be a scheme and $g : X \to \operatorname{Spec} R$ a morphism which is locally of finite type, locally quasi-finite, separated, quasi-compact and flat. Assume there is a point $x$ of $X$ whose image under the underlying continuous map of $g$ is the closed point of the local ring $R$, i.e. the closed fibre of $g$ is nonempty. Then $g$ admits a section: there exists a morphism $s : \operatorname{Spec} R \to X$ with $s$ followed by $g$ equal to the identity of $\operatorname{Spec} R$. No compatibility between $s$ and the given point $x$ is asserted; $x$ enters only as a witness that the closed fibre is nonempty.
--
--   This is the existence statement behind the usual combination of the structure theory of quasi-finite schemes over a henselian local ring with the valuative criterion of properness: over a henselian valuation ring with algebraically closed fraction field, a flat quasi-finite separated scheme with nonempty closed fibre has an $R$-point. It is used in the analysis of the Néron-model object attached to $J_0$ at $p$, in [`ModularCurve.JZeroNeronObjectAtP.exists_nsmul_eq`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_nsmul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] [Flat g]
    (x : X) (hx : g.base x = IsLocalRing.closedPoint R) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ := by sorry
