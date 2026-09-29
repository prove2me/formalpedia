-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split
-- name    : AlgebraicGeometry.Scheme.Modules.cocycle_of_forall_mapIso_eq_of_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bbf17851-23ef-573b-bee4-436b284170e3
-- title:
--   Cocycle condition for a split translation action
-- statement:
--   Fix schemes $X,Y$ and a morphism $q : X \to Y$, an additive group $G$ (of arbitrary universe), and a family $\sigma : G \to (X \to X)$ of self-maps of $X$ which is multiplicative for composition in the sense $\sigma(g+h) = \sigma_h \circ \sigma_g$. The splitting hypothesis `hsplit` concerns any scheme $Z$ and any pair $g_1,g_2 : Z \to X$ with $q \circ g_1 = q \circ g_2$: it produces a family of opens $U : G \to$ `Z.Opens` such that, as the condition is written (the $\bigsqcup_g$ ranges over the whole conjunction, so that it asserts the existence of one index with $U_g = \top$), some $U_g$ is all of $Z$ and, for every $g$, one has $g_2 \circ \iota_{U_g} = \sigma_g \circ g_1 \circ \iota_{U_g}$ on $U_g$. Let $M$ be a module on $X$, equipped with isomorphisms $\psi_g : M \cong \sigma_g^* M$ for all $g \in G$ satisfying the cocycle rule `hψadd`, namely that $\psi_{g+h}$ is $\psi_g$ followed by $\sigma_g^*\psi_h$, the comparison isomorphism $\sigma_g^*\sigma_h^* \cong (\sigma_g \circ \sigma_h)^*$ given by `Scheme.Modules.pullbackComp`, and the inverse of the transport isomorphism `Scheme.Modules.pullbackCongr` along $\sigma(g+h) = \sigma_g \ggg \sigma_h$. Further data: schemes $X''$, $X'''$; morphisms $a_1,a_2 : X'' \to X$ with $q \circ a_1 = q \circ a_2$; morphisms $b_{12},b_{13},b_{23} : X''' \to X''$ satisfying the three nerve identities $a_1 \circ b_{12} = a_1 \circ b_{13}$, $a_2 \circ b_{12} = a_1 \circ b_{23}$, $a_2 \circ b_{13} = a_2 \circ b_{23}$; and an isomorphism $\Psi : a_1^* M \cong a_2^* M$ subject to `hΨ`: for every $g \in G$ and every $w : W \to X''$ with $\sigma_g \circ a_1 \circ w = a_2 \circ w$, the pullback $w^*\Psi$ coincides, through the comparison isomorphisms for $w^*a_1^*$ and $w^*a_2^*$ and the transport along that equality, with $(a_1 \circ w)^*\psi_g$. The conclusion is the cocycle identity over $X'''$: the nine-term composite formed from the inverse of the transport along $h_1$, the inverse comparison for $b_{12}^*a_1^*$, $b_{12}^*\Psi$, the comparison for $b_{12}^*a_2^*$, the transport along $h_2$, the inverse comparison for $b_{23}^*a_1^*$, $b_{23}^*\Psi$, the comparison for $b_{23}^*a_2^*$ and the inverse transport along $h_3$ equals the three-term composite consisting of the inverse comparison for $b_{13}^*a_1^*$, $b_{13}^*\Psi$ and the comparison for $b_{13}^*a_2^*$; that is, $b_{23}^*\Psi \circ b_{12}^*\Psi = b_{13}^*\Psi$ read through the canonical identifications.
--
--   This is the Čech cocycle condition on $X''' \rightrightarrows X''$ for the isomorphism $\Psi$ glued from a $G$-equivariant structure on $M$ whose associated action is split in the above sense, and it is exactly the hypothesis required by the descent statement [`AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split), which realises $\Psi$ as a descent datum along $q$. The argument is local on $X'''$ and invokes [`AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover`](thm.html#AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover), the bijectivity of restriction of morphisms of modules to an open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.cocycle_of_forall_mapIso_eq_of_split
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm)
    {X'' X''' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M)
    (hΨ : ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm) :
    ((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app M) ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app M) ≪≫ ((Scheme.Modules.pullbackCongr h₃).app M).symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app M) := by sorry
