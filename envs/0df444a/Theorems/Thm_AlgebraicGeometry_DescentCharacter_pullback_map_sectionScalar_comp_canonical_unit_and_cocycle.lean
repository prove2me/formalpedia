-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
-- name    : AlgebraicGeometry.DescentCharacter.pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/9e12a473-21a6-5817-ac24-365b7095e438
-- title:
--   Multiplication by a unit-and-cocycle function gives a descent datum
-- statement:
--   Let $q\colon X\to Y$ be a morphism of schemes, let $p_1,p_2\colon P\to X$ satisfy $q\circ p_1=q\circ p_2$, let $\delta\colon X\to P$ be a common section, so $p_1\circ\delta=\mathrm{id}_X=p_2\circ\delta$, and let $a,b,c\colon P_3\to P$ satisfy $p_2\circ a=p_1\circ b$, $p_1\circ c=p_1\circ a$ and $p_2\circ c=p_2\circ b$. Let $M$ be an $\mathcal O_Y$-module, and let $u\in\Gamma(P,\mathcal O_P)$ satisfy $\delta^{*}u=1$ in $\Gamma(X,\mathcal O_X)$ and $a^{*}u\cdot b^{*}u=c^{*}u$ in $\Gamma(P_3,\mathcal O_{P_3})$, where $\delta^{*},a^{*},b^{*},c^{*}$ denote the maps on global sections. Let $\sigma$ be an endomorphism of $p_1^{*}q^{*}M$ which, on every open $U\subseteq P$ and every section $s$ over $U$, is multiplication by the restriction of $u$ to $U$. Set $\varphi:=\sigma$ followed by the canonical isomorphism $p_1^{*}q^{*}M\cong(q\circ p_1)^{*}M=(q\circ p_2)^{*}M\cong p_2^{*}q^{*}M$, the middle equality coming from $q\circ p_1=q\circ p_2$. The conclusion is the conjunction of two identities of morphisms of modules: the unit condition, that $\delta^{*}\varphi$, transported by the canonical isomorphisms attached to $p_1\circ\delta=\mathrm{id}$ and $p_2\circ\delta=\mathrm{id}$ and to composition of pullbacks, is the identity of $q^{*}M$; and the cocycle condition, that $a^{*}\varphi$ followed by $b^{*}\varphi$ (with the isomorphism coming from $p_2\circ a=p_1\circ b$ inserted between them) equals $c^{*}\varphi$, conjugated by the isomorphisms coming from $p_1\circ c=p_1\circ a$ and $p_2\circ c=p_2\circ b$.
--
--   This is the verification, in kernel-pair form, that multiplication by a global function satisfying the unit and cocycle identities defines a descent datum on the pullback of a module; no cartesianness or affineness hypothesis intervenes in this direction. It feeds the construction of a rigidified line bundle whose pullback under multiplication by two is trivial, used in the treatment of polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
    {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)
    (M : Y.Modules) (u : Γ(P, ⊤)) (hu₁ : δ.appTop u = 1) (hu₂ : a.appTop u * b.appTop u = c.appTop u)
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s) :
    let φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
        (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M) :=
      σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
          rw [hp]) ≫
        (Scheme.Modules.pullbackComp p₂ q).inv.app M)
    ((Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _) ∧
    (((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hab).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) := by sorry
