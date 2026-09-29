-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/cd78666d-28b6-5a95-8ca6-05f950d60c3d
-- title:
--   Chart divisibility by varpi of differentials from germ divisibility
-- statement:
--   Let $R$ be a commutative domain, $\varpi \in R$ a non-zero element whose principal ideal $(\varpi)$ is maximal, $\kappa$ a field and $q \colon R \to \kappa$ a ring homomorphism with $\ker q = (\varpi)$. Let $c \colon X \to \operatorname{Spec} R$ be a morphism of schemes that is smooth of relative dimension $1$, and let $\mathcal{V}$ be a two-chart affine open cover of $X$, that is, affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Assume the fibre product of $c$ with $\operatorname{Spec}(q)$ is an integral scheme, and let $x \in X$ lie in the image of the first projection of that fibre product. The two chart rings $\Gamma(X,U_0)$ and $\Gamma(X,U_1)$ carry the $R$-algebra structures induced by $c$ via $\Gamma\mathrm{Spec}$ and restriction from $\top$, and the stalk $\mathcal{O}_{X,x}$ carries the $R$-algebra structure given by the composite of the inverse of the $\Gamma\mathrm{Spec}$ isomorphism for $R$, the map $c$ on global sections, and the germ map at $x$ on $\top$; the hypotheses `hc0` and `hc1` say that, whenever $x \in U_i$, the germ homomorphism $\Gamma(X,U_i) \to \mathcal{O}_{X,x}$ is compatible with these structures, i.e. composing it with the structure map $R \to \Gamma(X,U_i)$ gives the structure map $R \to \mathcal{O}_{X,x}$ (precomposed with the identity of $R$). The conclusion is the conjunction, over $i = 0, 1$, of the following: for every proof that $x \in U_i$, every $\omega_i \in \Omega_{\Gamma(X,U_i)/R}$ and every $\eta \in \Omega_{\mathcal{O}_{X,x}/R}$, if the map on Kähler differentials induced by the identity of $R$ and the germ homomorphism sends $\omega_i$ to $\varpi \cdot \eta$, then $\omega_i = \varpi \cdot \alpha$ for some $\alpha \in \Omega_{\Gamma(X,U_i)/R}$.
--
--   This is the chart-level descent of $\varpi$-divisibility for relative differentials on a smooth relative curve with integral special fibre: divisibility of the germ at a point of that fibre forces divisibility on the whole chart, the stalk being a localisation of the chart ring at the prime of $x$ and $\Omega_{\Gamma(X,U_i)/R}$ being projective. It feeds the corresponding statement for the Čech $H^0$ of the sheaf of relative differentials attached to a two-chart cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (x : X) (hx : x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base)
    (hc0 : ∀ h0 : x ∈ 𝒱.U0, ((X.presheaf.germ 𝒱.U0 x h0).hom : (𝒱.cover c).A0 →+* X.presheaf.stalk x).comp
        (algebraMap R (𝒱.cover c).A0) =
      ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).comp
        (RingHom.id R))
    (hc1 : ∀ h1 : x ∈ 𝒱.U1, ((X.presheaf.germ 𝒱.U1 x h1).hom : (𝒱.cover c).A1 →+* X.presheaf.stalk x).comp
        (algebraMap R (𝒱.cover c).A1) =
      ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).comp
        (RingHom.id R)) :
    letI : Algebra R (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    (∀ (h0 : x ∈ 𝒱.U0) (ω₀ : Ω[(𝒱.cover c).A0⁄R]) (η : Ω[X.presheaf.stalk x⁄R]),
        KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A0) (B := X.presheaf.stalk x)
          (RingHom.id R) (X.presheaf.germ 𝒱.U0 x h0).hom (hc0 h0) ω₀ = ϖ • η →
        ∃ α : Ω[(𝒱.cover c).A0⁄R], ω₀ = ϖ • α) ∧
    (∀ (h1 : x ∈ 𝒱.U1) (ω₁ : Ω[(𝒱.cover c).A1⁄R]) (η : Ω[X.presheaf.stalk x⁄R]),
        KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := X.presheaf.stalk x)
          (RingHom.id R) (X.presheaf.germ 𝒱.U1 x h1).hom (hc1 h1) ω₁ = ϖ • η →
        ∃ α : Ω[(𝒱.cover c).A1⁄R], ω₁ = ϖ • α) := by sorry
