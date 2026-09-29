-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split
-- name    : AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_forall_mapIso_eq_of_free_of_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/55cfd760-3e6f-5d7b-91b0-b703302f7338
-- title:
--   Gluing a family of pullback isomorphisms over a pair equalised by q
-- statement:
--   Let $q : X \to Y$ be a morphism of schemes, let $G$ be an additive group, and let $\sigma : G \to \operatorname{Hom}(X,X)$ satisfy $\sigma_0 = \mathrm{id}_X$ and $\sigma_{g+h} = \sigma_h \circ \sigma_g$. Two hypotheses are imposed on this action: freeness, namely that for every scheme $Z$, every $v : Z \to X$ and every $g \in G$, if $Z$ has a point and $\sigma_g \circ v = v$ then $g = 0$; and splitting, namely that whenever $g_1, g_2 : Z \to X$ satisfy $q \circ g_1 = q \circ g_2$ there is a family of opens $U : G \to Z.\mathrm{Opens}$ with $\bigsqcup_g U_g = \top$ and $g_2|_{U_g} = \sigma_g \circ g_1|_{U_g}$ for each $g$. Let $M$ be a sheaf of modules on $X$ and let $\psi_g : M \cong \sigma_g^* M$ be isomorphisms, one for each $g \in G$ (no cocycle compatibility is assumed). Then for any $a_1, a_2 : X'' \to X$ with $q \circ a_1 = q \circ a_2$ there is an isomorphism $\Psi : a_1^* M \cong a_2^* M$ which is locally given by $\psi$: for every $g$ and every $w : W \to X''$ with $\sigma_g \circ a_1 \circ w = a_2 \circ w$, the pullback $w^*\Psi$ equals the composite $w^* a_1^* M \cong (a_1 w)^* M \xrightarrow{(a_1w)^*\psi_g} (a_1w)^*\sigma_g^* M \cong (\sigma_g a_1 w)^* M = (a_2 w)^* M \cong w^* a_2^* M$ of the canonical comparison isomorphisms `pullbackComp`, `pullbackCongr` and $(a_1w)^*\psi_g$.
--
--   This is the gluing half of the passage from a cocycle for a free, split action of $G$ on $X$ over $Y$ to a descent datum for $q$ in the sense of Grothendieck's descent theory: the local prescriptions $\psi_g$ on the pieces of the splitting cover of $X''$ are assembled into a single isomorphism between the two pullbacks. It feeds [`AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split), and its proof cites the gluing of module morphisms along a pairwise disjoint open cover and the bijectivity of the descent-data map for an open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_forall_mapIso_eq_of_free_of_split
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσ0 : σ 0 = 𝟙 X) (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hfree : ∀ ⦃Z : Scheme.{u}⦄ (v : Z ⟶ X) (g : G), Nonempty ↥Z → v ≫ σ g = v → g = 0)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    {X'' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q) :
    ∃ Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M,
      ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm := by sorry
