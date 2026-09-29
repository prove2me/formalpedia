-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
-- name    : AlgebraicGeometry.SplitTorus.exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/19b02fb2-542d-5666-99d8-c52b9677ec24
-- title:
--   Split torus: commutative group law, unit points, finite flat [n]
-- statement:
--   Let $S$ be a commutative ring and $d$ a natural number; write $S[\mathbb Z^d]$ for the additive monoid algebra `torusCoord S d` of $\mathbb Z^d = (\mathrm{Fin}\,d \to \mathbb Z)$ over $S$, and let `torusStr S d` be the structure morphism $\operatorname{Spec} S[\mathbb Z^d] \to \operatorname{Spec} S$ obtained by applying $\operatorname{Spec}$ to $S \to S[\mathbb Z^d]$. The assertion is that there exists a relative group law $L$ on this morphism — that is, for every scheme $T$ and every $t : T \to \operatorname{Spec} S$ a multiplication, unit and inversion on the set of $\varphi : T \to \operatorname{Spec} S[\mathbb Z^d]$ with $\varphi$ followed by `torusStr S d` equal to $t$, satisfying associativity, the unit laws, left inversion and compatibility with precomposition by morphisms $T' \to T$ over $\operatorname{Spec} S$ — with the following five properties. (i) $L$ is commutative. (ii) For every $T$ and every $t : T \to \operatorname{Spec} S$ there is a bijection $e$ from the points of `torusStr S d` over $t$ to $d$-tuples of units of $\Gamma(T,\top)$ whose $i$-th coordinate is the image of the monomial $X^{\mathrm{e}_i} =$ `AddMonoidAlgebra.single (Pi.single i 1) 1` under the ring homomorphism $S[\mathbb Z^d] \to \Gamma(T,\top)$ given by the inverse of `Scheme.ΓSpecIso` followed by the map on global sections of $\varphi$, and which carries the multiplication of $L$ to coordinatewise multiplication of units. (iii) For every $S$-algebra $S'$ and all $\chi, \chi'$ in the monoid `WithConv` on the $S$-algebra homomorphisms $S[\mathbb Z^d] \to S'$, the point `torusPt` attached to the underlying homomorphism of $\chi\chi'$ (i.e. $\operatorname{Spec}$ of it, viewed as a point over $\operatorname{Spec} S' \to \operatorname{Spec} S$) is the $L$-product of the points attached to $\chi$ and $\chi'$. (iv) The point attached to the underlying homomorphism of $1$ in that monoid is the $L$-unit. (v) For every $n$, the morphism `L.schemeNsmul n` — the underlying morphism $\operatorname{Spec} S[\mathbb Z^d] \to \operatorname{Spec} S[\mathbb Z^d]$ of the $n$-fold $L$-sum of the identity point, defined by recursion from the unit — equals $\operatorname{Spec}$ of the ring homomorphism induced on monoid algebras by the endomorphism $n \cdot \mathrm{id}$ of $\mathbb Z^d$; and for $n > 0$ this morphism is finite and flat.
--
--   This is the standard group scheme structure on the split torus $\mathbb G_m^d$ over an arbitrary commutative base ring, in functor-of-points form: $T$-points are $d$-tuples of units of $\Gamma(T,\mathcal O_T)$, algebra-valued points multiply by convolution of characters, and $[n]$ is the monomial map $X^v \mapsto X^{nv}$, which is finite and flat for $n \geq 1$. It supplies the torus input for the statements about closed immersions of the special fibre of $X_1(p)$-related schemes into a split torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
    (S : Type u) [CommRing S] (d : ℕ) :
    ∃ L : RelativeGroupLaw S (torusStr S d),
      L.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
        ∃ e : SchemeHomOver t (torusStr S d) ≃ (Fin d → Γ(T, ⊤)ˣ),
          (∀ (x : SchemeHomOver t (torusStr S d)) (i : Fin d),
            (e x i : Γ(T, ⊤)) =
              ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord S d))).inv ≫ x.1.appTop).hom
                (AddMonoidAlgebra.single (Pi.single i 1) 1)) ∧
          (∀ x y : SchemeHomOver t (torusStr S d), e (L.mul t x y) = e x * e y)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra S S'] (χ χ' : WithConv (torusCoord S d →ₐ[S] S')),
        torusPt S S' d (χ * χ').ofConv =
          L.mul _ (torusPt S S' d χ.ofConv) (torusPt S S' d χ'.ofConv)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra S S'],
        torusPt S S' d (1 : WithConv (torusCoord S d →ₐ[S] S')).ofConv = L.one _) ∧
      (∀ n : ℕ, L.schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin d → ℤ))))) ∧
      (∀ n : ℕ, 0 < n → IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n)) := by sorry
