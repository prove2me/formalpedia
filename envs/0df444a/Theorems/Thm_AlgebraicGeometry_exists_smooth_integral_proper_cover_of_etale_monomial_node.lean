-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_integral_proper_cover_of_etale_monomial_node
-- name    : AlgebraicGeometry.exists_smooth_integral_proper_cover_of_etale_monomial_node
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-29T02:49:46.980586+00:00
-- url     : https://prove2.me/theorems/e493a9ed-2585-4e32-bdff-09295be79676
-- title:
--   Smooth integral proper covers of integral etale monomial-node charts
-- statement:
--   Let $K$ be a commutative integral domain, let $I$ be a finite set of variables, and let $d_i$ be nonnegative integer exponents. Set
--   $$N_d=\operatorname{Spec}\bigl(K[(t_i)_{i\in I},u,v]/(uv-\prod_{i\in I}t_i^{d_i})\bigr),$$
--   and let $\pi:N_d\to\operatorname{Spec}K$ be its coefficient structure map. For every integral scheme $C$ with an etale morphism $g:C\to N_d$, there exist an integral scheme $Y$ and a proper surjective morphism
--   $$q:Y\longrightarrow C$$
--   such that $\pi\circ g\circ q$ is smooth. Over the whole inverse image $C_u=g^{-1}(D(u))$, the restriction is an isomorphism:
--   $$q^{-1}(C_u)\xrightarrow{\sim}C_u.$$
--   There is no extra hypothesis that $C_u$ is nonempty: this follows from the etale chart and the monomial-node model. The unit monomial and empty variable set are included. No field, characteristic, perfectness, regularity or noetherianity hypothesis on $K$ is imposed.
--
--   This transports the affine monomial proper smooth-cover construction to integral etale charts. Compatible global projective modifications and alterations of arbitrary families remain further assertions.
-- source:
--   Derived etale-local transport of the affine polynomial monomial-node construction motivated by A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathematiques de l’IHES 83 (1996), Sections 3.3–3.6, pp. 63–65; https://www.numdam.org/article/PMIHES_1996__83__51_0.pdf . This is an auxiliary local proper-cover assertion, not a verbatim numbered theorem. It reuses the Proved monomial-cover theorem 5b605de5-d892-4596-b119-76ba187fb468 and the Proved reducedness theorem 000684d8-883f-5c97-94f5-ab16d639e585. The pullback is reduced by flatness and formal unramifiedness over the integral covering scheme, and its dense open is isomorphic to a nonempty open of the integral chart. No global projectivity, descent of the chosen modification, or blowup identification is asserted.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
universe u

theorem AlgebraicGeometry.exists_smooth_integral_proper_cover_of_etale_monomial_node
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ)
    (V : Scheme.{u}) [IsIntegral V]
    (g : V ⟶ Spec (.of (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))))
    [Etale g] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ V),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ g ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K)))) ∧
      IsIso (q ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (MvPolynomial.monomial d (1 : K)))) := by sorry
