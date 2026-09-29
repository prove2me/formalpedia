-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split
-- name    : AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/79742f35-2b34-5449-8be4-d6a570bf0664
-- title:
--   Descent datum from a cocycle for a free split action
-- statement:
--   Let $q : X \to Y$ be a morphism of schemes, let $G$ be an additive group and let $\sigma : G \to \operatorname{Hom}(X,X)$ satisfy $\sigma_0 = \mathrm{id}_X$ and $\sigma_{g+h} = \sigma_h \circ \sigma_g$ (i.e. $\sigma_g$ followed by $\sigma_h$), so that $G$ acts on $X$ over the base. Assume the action is free in the scheme-theoretic sense that for every scheme $Z$, every $v : Z \to X$ and every $g \in G$, if $Z$ is nonempty and $v \circ \sigma_g = v$ then $g = 0$; and that it splits the kernel pairs of $q$: for all $g_1, g_2 : Z \to X$ with $q \circ g_1 = q \circ g_2$ there is a family of open subschemes $U_g \subseteq Z$ ($g \in G$) with $\bigsqcup_g U_g = \top$ and with $g_2$ agreeing with $\sigma_g \circ g_1$ after restriction along the inclusion $U_g \hookrightarrow Z$. Let $M$ be an object of `X.Modules` together with isomorphisms $\psi_g : M \cong \sigma_g^* M$ such that $\psi_0$ is the canonical isomorphism obtained from `pullbackId` and `pullbackCongr` applied to $\sigma_0 = \mathrm{id}_X$, and such that $\psi_{g+h}$ equals $\psi_g$ followed by $\sigma_g^*\psi_h$ and the canonical comparison isomorphisms `pullbackComp` and `pullbackCongr` for $\sigma_{g+h} = \sigma_g \circ \sigma_h$ (reversed). Then there exists a descent datum $D$ for the pseudofunctor `Scheme.Modules.pseudofunctor` composed with `Bicategory.Adj.forget₁`, relative to the one-member family of morphisms indexed by `Unit` with constant value $q$, whose underlying object $D.\mathrm{obj}\, i$ equals $M$ for every index $i$.
--
--   This is the descent datum attached to a module equipped with a $G$-equivariant structure, for a quotient map $q$ whose kernel pairs are split by a free $G$-action: the classical step in descent along a free quotient by a group acting by translations. It is used in the construction of line bundles and Riemann forms on abelian schemes, being cited by the results on descent data for multiplication-by-$n$ and on invertible pullbacks along translations by torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσ0 : σ 0 = 𝟙 X) (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hfree : ∀ ⦃Z : Scheme.{u}⦄ (v : Z ⟶ X) (g : G), Nonempty ↥Z → v ≫ σ g = v → g = 0)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψ0 : ψ 0 = ((Scheme.Modules.pullbackId X).app M).symm ≪≫ ((Scheme.Modules.pullbackCongr hσ0).app M).symm)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm) :
    ∃ D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => q),
      ∀ i, D.obj i = M := by sorry
