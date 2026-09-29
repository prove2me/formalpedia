-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point
-- name    : AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/275aaee5-decb-5555-bbef-1cfa014ceb47
-- title:
--   Rigidity of Pic⁰-endomorphisms from ℚ̄-points
-- statement:
--   Fix a prime $\ell$ and write $R = \mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Let $c : X \to \operatorname{Spec} R$ be a morphism of schemes (in universe $0$) that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to X$ whose composite with $c$ is the identity. Let $D$ be a `RelativePic0Designation` for $c$: a scheme $D.P$ with a structure morphism $D.\mathrm{toBase} : D.P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it. Assume $hD$: the datum $D$ represents the $\varepsilon$-rigidified relative Picard presheaf of $c$ cut out by `algEquivZeroCut c ε`; that is, there is a Poincaré rigidified invertible module on $X \times_{\operatorname{Spec} R} D.P$ which is fibrewise algebraically equivalent to zero (for every algebraically closed field $k$ and every $k$-point of the base, its restriction to the corresponding fibre is connected to the trivial bundle by a family over a geometrically integral, locally of finite type $k$-scheme with two sections), such that for every $R$-scheme $t : T \to \operatorname{Spec} R$ and every rigidified invertible module on $X \times_{\operatorname{Spec} R} T$ with that fibrewise property there is a unique $R$-morphism $T \to D.P$ pulling the Poincaré bundle back to it, and such that the pullback along the zero section is trivial. Assume further that $D.\mathrm{toBase}$ is smooth ($hsm$), proper ($hpr$) and geometrically connected ($hgc$). Then for any two endomorphisms $\varphi, \psi$ of $D.P$ over $\operatorname{Spec} R$ (morphisms $D.P \to D.P$ whose composite with $D.\mathrm{toBase}$ is $D.\mathrm{toBase}$), if for every $\overline{\mathbb{Q}}$-point $x : \operatorname{Spec}\overline{\mathbb{Q}} \to D.P$ over the structure map $\operatorname{Spec}$ of $R \to \overline{\mathbb{Q}}$ one has $x$ followed by $\varphi$ equal to $x$ followed by $\psi$, then $\varphi = \psi$ as $R$-morphisms.
--
--   This is the standard rigidity statement that a morphism between schemes of finite type over a base with dense generic fibre is determined by its values on geometric points, specialised to endomorphisms of a scheme representing the algebraic-equivalence-to-zero part of the rigidified relative Picard functor of a proper smooth relative curve over $\mathbb{Z}_{(\ell)}$; unlike textbook rigidity lemmas for abelian schemes, no compatibility with a group law is assumed of $\varphi$ and $\psi$, only agreement on $\overline{\mathbb{Q}}$-points. The representability hypothesis and the smoothness, properness and geometric connectedness of $D.\mathrm{toBase}$ are carried as explicit binders, matching the datum produced by the construction of the relative Jacobian of $X_0(p)$. It is used to identify endomorphisms of that relative Jacobian which are specified only on geometric points, for instance in establishing the Hecke action on the relative Jacobian over $\mathbb{Z}_{(\ell)}$ at a point corresponding to $j = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by sorry
