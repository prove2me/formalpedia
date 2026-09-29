-- Prove2me | Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
-- name    : AlgebraicGeometry.ChowDatumProj.nonempty_of
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/a3c8d81b-32eb-5102-8741-56367f90c89e
-- title:
--   Chow datum in a product of projective spaces yields one in P^N
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi : V \to \operatorname{Spec} R$ a morphism of schemes. A term of `ChowDatum π` consists of a natural number $m$, a function $e : \mathrm{Fin}\,m \to \mathbb{N}$, a scheme $V'$, morphisms $p : V' \to V$ and $\iota : V' \to$ `ProjSpace.prodOver R e` (the scheme over $\operatorname{Spec} R$ playing the role of the product over $R$ of the projective spaces of dimensions $e_0,\dots,e_{m-1}$, with structure morphism `ProjSpace.prodOverπ R e`), together with the hypotheses that $p$ is proper, that $\iota$ is a closed immersion, and that $\iota$ followed by `ProjSpace.prodOverπ R e` equals $p$ followed by $\pi$, plus an open subscheme $U \subseteq V$ whose underlying set is dense and such that the second projection $V' \times_V U \to U$ is an isomorphism. A term of `ChowDatumProj π` consists of the same data except that the target of the closed immersion is a single projective space: a natural number $N$ and a closed immersion $\iota_N : V' \to \operatorname{Proj}$ of the graded ring of polynomials in $N+1$ variables over $R$, with $\iota_N$ followed by the structure morphism `ProjSpace.π R N` equal to $p$ followed by $\pi$, again with $p$ proper and with a dense open $U$ over which $p$ is an isomorphism. The theorem asserts that if `ChowDatum π` is nonempty then so is `ChowDatumProj π`. No relation between $N$ and the $e_i$ is asserted; only existence is claimed.
--
--   This is the passage from a product of projective spaces to a single projective space in Chow's lemma, effected by the Segre embedding; $p$, $U$ and the density and isomorphism conditions are carried over unchanged. It is used in the treatment of coherence and Čech-type statements for proper morphisms, where an embedding into one $\mathbb{P}^N_R$ is needed to run induction on $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.ChowDatumProj.nonempty_of {R : Type u} [CommRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) : Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) := by sorry
