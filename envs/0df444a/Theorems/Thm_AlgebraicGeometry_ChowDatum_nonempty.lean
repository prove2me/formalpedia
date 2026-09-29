-- Prove2me | Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
-- name    : AlgebraicGeometry.ChowDatum.nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/82983144-f2fc-56a9-a75e-db25c67d29fd
-- title:
--   Chow's lemma for proper integral schemes over a Noetherian ring
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $V$ be a scheme which is integral, and let $\pi : V \to \operatorname{Spec}(R)$ be a proper morphism (properness and integrality being typeclass hypotheses). The assertion is that the type `ChowDatum π` is nonempty, i.e. there exist: a natural number $m$; a function $e : \mathrm{Fin}\,m \to \mathbb{N}$ assigning an exponent to each index; a scheme $V'$; morphisms $p : V' \to V$ and $\iota : V' \to$ `ProjSpace.prodOver R e`, where the latter scheme is the product over $R$ of the projective spaces of dimensions $e_0,\dots,e_{m-1}$ equipped with its structure morphism `ProjSpace.prodOverπ R e` to $\operatorname{Spec}(R)$; together with the data that $p$ is proper, that $\iota$ is a closed immersion, and that $\iota$ followed by `ProjSpace.prodOverπ R e` equals $p$ followed by $\pi$; and finally an open subscheme $U$ of $V$ whose underlying set is dense in $V$, such that the second projection $V' \times_V U \to U$ of $p$ along the open immersion $U \hookrightarrow V$ is an isomorphism.
--
--   This is Chow's lemma in the integral case: a proper integral scheme over a Noetherian ring admits a proper morphism from a scheme that is a closed subscheme of a product of projective spaces over $R$, which is an isomorphism over a dense open subset (so in particular birational). It is used in the project in the cohomological study of coherent sheaves on proper schemes, namely in [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih) and in [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete), where dévissage along such a dominating projective scheme is performed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ChowDatum_nonempty.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.ChowDatum.nonempty {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) [IsProper π] [IsIntegral V] : Nonempty (ChowDatum π) := by sorry
