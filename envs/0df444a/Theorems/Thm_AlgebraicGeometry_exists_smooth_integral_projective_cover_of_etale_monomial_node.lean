-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_integral_projective_cover_of_etale_monomial_node
-- name    : AlgebraicGeometry.exists_smooth_integral_projective_cover_of_etale_monomial_node
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-29T15:27:39.240915+00:00
-- url     : https://prove2.me/theorems/1140c6bb-0b13-4efc-8acb-55b6f3531b13
-- title:
--   Projective smooth integral covers of integral etale monomial-node charts
-- statement:
--   Let $K$ be a commutative integral domain, let $I$ be a finite set of variables, and let $d_i$ be nonnegative integer exponents. Put
--   $$N_d=\operatorname{Spec}\bigl(K[(t_i)_{i\in I},u,v]/(uv-\prod_{i\in I}t_i^{d_i})\bigr).$$
--   For every integral scheme $C$ with an etale morphism $g:C\to N_d$, there exist an integral scheme $Y$ and a proper surjective morphism $q:Y\to C$ such that the composite $Y\to C\to N_d\to\operatorname{Spec}K$ is smooth. The same morphism is projective: for some $n\geq0$ there is a closed immersion into the actual base-changed projective space
--   $$j:Y\hookrightarrow C\times_{N_d}\mathbb P^n_{N_d},\qquad \operatorname{pr}_C\circ j=q.$$
--   On $C_u=g^{-1}(D(u))$, the complete restriction is an isomorphism:
--   $$q^{-1}(C_u)\xrightarrow{\sim}C_u.$$
--   Nonemptiness of $C_u$ is a consequence, not an additional hypothesis. The unit monomial and empty variable set are included. No field, characteristic, perfectness, regularity or noetherianity assumption on $K$ is required, and $C$ need not be affine.
--
--   This transports the projective affine monomial-node cover to integral etale charts. Compatibility of modifications chosen on overlapping charts and the construction of a global alteration remain separate assertions.
-- source:
--   Derived etale base-change corollary of the affine projective monomial-node construction motivated by A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathematiques de l’IHES 83 (1996), Sections 3.3–3.6, pp. 63–65; https://www.numdam.org/article/PMIHES_1996__83__51_0.pdf . This is an auxiliary local projective-cover result, not a verbatim numbered assertion. It reuses the Proved projective monomial-node theorem 79d087d7-23e7-42f3-8278-664c95c82441 and the Proved reducedness theorem 000684d8-883f-5c97-94f5-ab16d639e585. The covering source and its closed embedding are actual fibre products; reducedness and a dense integral open give integrality. No compatible descent across etale overlaps or global alteration is asserted.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
universe u

theorem AlgebraicGeometry.exists_smooth_integral_projective_cover_of_etale_monomial_node
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ)
    (V : Scheme.{u}) [IsIntegral V]
    (g : V ⟶ Spec (.of (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))))
    [Etale g] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ V),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ g ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K)))) ∧
      IsIso (q ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (monomial d (1 : K)))) ∧
      ∃ (N : ℕ) (j : Y ⟶ pullback g
          (ProjSpace.π (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K))) N)),
        IsClosedImmersion j ∧ j ≫ pullback.fst _ _ = q := by sorry
