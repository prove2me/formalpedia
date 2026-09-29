-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_isSectionBasis_app_pullbackLocalSection_of_isSectionBasis
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.isSectionBasis_app_pullbackLocalSection_of_isSectionBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/cb0e2c16-9de1-5906-beac-d07b961fb111
-- title:
--   Section bases persist under base change of a polarisation
-- statement:
--   Fix natural numbers $g,d,n$, a commutative ring $S$ and $u : \mathtt{PolarisedAbelianScheme}\ g\ d\ n\ S$, i.e. a scheme $A$ with a structure morphism $u.f : A \to \operatorname{Spec} S$, a commutative relative group law, an abelian-scheme property bundle, all fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections over $\operatorname{Spec} S$ that generate the $n$-torsion freely on geometric fibres over algebraically closed fields, and a module $u.\mathrm{pol}$ on $A$ that is invertible, defines a closed immersion by sections over $S$, and has geometric fibrewise $H^0$-rank $d$. Let $R, R'$ be commutative rings, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, $t' : \operatorname{Spec} R' \to \operatorname{Spec} S$ and $\psi : R \to R'$ a ring homomorphism with $\operatorname{Spec}(\psi)$ followed by $t$ equal to $t'$. Let $b$ be a morphism from the pullback of $u.f$ along $t'$ to the pullback along $t$ that commutes with the first projections and satisfies $b$ followed by the second projection equal to the second projection followed by $\operatorname{Spec}(\psi)$, and let $c$ be an isomorphism of modules from $b^\ast$ of the pullback of $u.\mathrm{pol}$ to $A_R$ to the pullback of $u.\mathrm{pol}$ to $A_{R'}$. Suppose $\sigma : \mathrm{Fin}\,m \to \Gamma$ of the pulled-back polarisation on $A_R$ is a section basis for the structure map to $\operatorname{Spec} R$, meaning that $c \mapsto \sum_i \bar c_i \cdot \sigma_i$ is a bijection from $\mathrm{Fin}\,m \to R$ onto global sections, scalars being taken via the structure map. Then the family $i \mapsto c(b^\ast \sigma_i)$, the global-section component of $c$ applied to the pullback along $b$ of $\sigma_i$, is a section basis over $R'$ for the pulled-back polarisation on $A_{R'}$.
--
--   This is the base-change invariance of a basis of global sections of a polarisation along a change of affine base, in the form needed to propagate an explicit frame of theta-like sections from one base ring to another. It is used in the construction of Schrödinger frames for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_isSectionBasis_app_pullbackLocalSection_of_isSectionBasis.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.isSectionBasis_app_pullbackLocalSection_of_isSectionBasis
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R R' : Type} [CommRing R] [CommRing R'] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (ψ : R →+* R')
    (hr : Spec.map (CommRingCat.ofHom ψ) ≫ t = t')
    (b : pullback u.f t' ⟶ pullback u.f t) (hb₁ : b ≫ pullback.fst u.f t = pullback.fst u.f t')
    (hb₂ : b ≫ pullback.snd u.f t = pullback.snd u.f t' ≫ Spec.map (CommRingCat.ofHom ψ))
    (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) ≅
      (Scheme.Modules.pullback (pullback.fst u.f t')).obj u.pol)
    {m : ℕ} (σ : Fin m → Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤))
    (hσ : Scheme.Modules.IsSectionBasis (pullback.snd u.f t) ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) σ) :
    Scheme.Modules.IsSectionBasis (pullback.snd u.f t') ((Scheme.Modules.pullback (pullback.fst u.f t')).obj u.pol)
      (fun i => c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (σ i) :
        Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol), ⊤))) := by sorry
