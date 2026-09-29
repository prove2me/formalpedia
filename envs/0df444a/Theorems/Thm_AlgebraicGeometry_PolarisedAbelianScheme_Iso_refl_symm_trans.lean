-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/c8179ae6-b57c-5057-9661-0840f6e5f08e
-- title:
--   Isomorphism of polarised abelian schemes is an equivalence relation
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and a commutative ring $S$. An object of `PolarisedAbelianScheme g d n S` consists of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on the functor of $T$-points of $f$, the property bundle of `AbelianSchemePropertyBundle` (smoothness, properness, connected fibres, existence of a relative group law), fibres of topological Krull dimension $g$, a family $P : \mathrm{Fin}(2g) \to$ sections of $f$ that are killed by $n$ and form a basis of the $n$-torsion on every geometric fibre (injectivity and surjectivity of the $\mathrm{Fin}\,n$-linear combination map over algebraically closed fields), together with a module `pol` on $A$ that is invertible, realises a closed immersion into projective space by its sections, and has geometric fibrewise $H^0$-rank $d$. For two such objects, `PolarisedAbelianScheme.Iso u u'` asserts the existence of an isomorphism $e : u.A \cong u'.A$ with $e_{\hom}$ followed by $u'.f$ equal to $u.f$, compatible with the group laws on all $T$-points, carrying each $P_i$ to the corresponding section of $u'$, and such that each point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which the pullback of $u'$'s polarisation along $e_{\hom}$, restricted to $u.f^{-1}(U)$, is isomorphic to the restriction of $u$'s polarisation. The theorem asserts the conjunction of three statements: this relation is reflexive, symmetric and transitive; it is phrased as a conjunction rather than as an `Equivalence` or `Setoid` instance.
--
--   This records that the notion of isomorphism used for polarised abelian schemes with level structure behaves as an equivalence relation, so that isomorphism classes of such objects may be manipulated freely. It is cited by the results establishing isomorphism of polarised abelian schemes from pointwise or local data, for instance [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_forall_away_iso`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_forall_away_iso) and [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.iso_of_pt_eq_of_finite_free_transitive`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.iso_of_pt_eq_of_finite_free_transitive).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans
    {g d n : ℕ} {S : Type} [CommRing S] :
    (∀ u : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.Iso u u) ∧
    (∀ u v : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v u) ∧
    (∀ u v w : PolarisedAbelianScheme g d n S,
      PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v w → PolarisedAbelianScheme.Iso u w) := by sorry
