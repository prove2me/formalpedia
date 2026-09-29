-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
-- name    : AlgebraicGeometry.Scheme.exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/531ef877-2df3-5901-b570-de975cc3665d
-- title:
--   Formal smoothness of the stalk map via an affine chart
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $M$ be a scheme (in the zeroth universe), let $\varpi : M \to \operatorname{Spec} R$ be a morphism that is locally of finite type, and let $x$ be a point of $M$ whose singleton is closed in $M$. The assertion is that there exist a natural number $n$, two ideals $I \le J$ of the polynomial ring $P = R[X_i : i \in \mathrm{Fin}\,n]$ with $J$ maximal, such that the image $J/I$ of $J$ in $P/I$ is prime, together with an open immersion $\iota : \operatorname{Spec}(P/I) \to M$ satisfying three conditions: $\iota$ followed by $\varpi$ equals the morphism $\operatorname{Spec}$ of the structure map $R \to P/I$; the underlying map of $\iota$ sends the point of $\operatorname{Spec}(P/I)$ given by the prime $J/I$ to $x$; and, if the localisation $(P/I)_{J/I}$ at that prime is a formally smooth $R$-algebra, then the ring homomorphism $\varpi^{\sharp}_x : \mathcal{O}_{\operatorname{Spec} R,\,\varpi(x)} \to \mathcal{O}_{M,x}$ induced by $\varpi$ on stalks is formally smooth. Thus formal smoothness of the stalk map at $x$ is reduced to a statement about an explicitly presented localised finitely generated $R$-algebra.
--
--   This is the chart-producing step that converts a local question about a closed point of a scheme locally of finite type over a Noetherian base into a question about a localisation of a quotient of a polynomial ring. It is used in the proofs that a morphism is smooth from a lifting criterion over Artinian test rings, namely [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int) and [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType ϖ] (x : ↥M) (hx : IsClosed ({x} : Set ↥M)) :
    ∃ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
      (hJI : (J.map (Ideal.Quotient.mk I)).IsPrime)
      (ι : Spec (CommRingCat.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ M) (_ : IsOpenImmersion ι),
      ι ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))) ∧
      ι.base ⟨J.map (Ideal.Quotient.mk I), hJI⟩ = x ∧
      (Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) →
          (ϖ.stalkMap x).hom.FormallySmooth) := by sorry
