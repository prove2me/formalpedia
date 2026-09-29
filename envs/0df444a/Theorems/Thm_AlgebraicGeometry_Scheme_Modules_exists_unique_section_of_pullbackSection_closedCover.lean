-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
-- name    : AlgebraicGeometry.Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/76eab2c0-1d86-5754-bd6c-da784a1cdcb8
-- title:
--   Sections over a reduced scheme covered by two closed subschemes
-- statement:
--   Let $X$, $Z_1$, $Z_2$ be schemes, let $i_1 : Z_1 \to X$ and $i_2 : Z_2 \to X$ be closed immersions, and assume $X$ is reduced and that the images of the underlying continuous maps of $i_1$ and $i_2$ cover $X$, i.e. $\operatorname{range}(i_1)\cup\operatorname{range}(i_2)$ is all of the space of $X$. Let $L$ be a sheaf of modules on $X$ satisfying `Scheme.Modules.IsInvertible`, that is: every point of $X$ has an open neighbourhood $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules of $U$. Let $\sigma_1 : \mathbf{1} \to i_1^{*}L$ and $\sigma_2 : \mathbf{1} \to i_2^{*}L$ be global sections, i.e. maps from the monoidal unit of the category of modules on $Z_1$, resp. $Z_2$, and assume that they agree on the fibre product $Z_1 \times_X Z_2$: the section $\sigma_1$ pulled back along the first projection, followed by the comparison isomorphism `pullbackComp` for that projection with $i_1$ at $L$ and then by the isomorphism `pullbackCongr` attached to the equality of the two composites $Z_1\times_X Z_2 \to X$, coincides with the section $\sigma_2$ pulled back along the second projection followed by the corresponding `pullbackComp` isomorphism at $L$. Here the pullback of a global section $s$ along $F$ means $F^{*}s$ composed with the inverse of the canonical isomorphism identifying the pullback of the unit with the unit. The conclusion is that there exists a global section $\sigma : \mathbf{1} \to L$ on $X$ whose pullbacks along $i_1$ and $i_2$ are $\sigma_1$ and $\sigma_2$, and that any global section $\sigma'$ with these two pullback properties equals $\sigma$.
--
--   This is the module-theoretic form of the Milnor-square description of a reduced scheme covered by two closed subschemes: sections of an invertible sheaf on $X$ correspond to pairs of sections on $Z_1$ and $Z_2$ agreeing on the scheme-theoretic intersection $Z_1\times_X Z_2$. It is used to produce trivialisations of invertible sheaves built from data on the two pieces, and in the analysis of curves obtained by gluing two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover
    {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced X]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (σ₁ : 𝟙_ Z₁.Modules ⟶ (Scheme.Modules.pullback i₁).obj L) (σ₂ : 𝟙_ Z₂.Modules ⟶ (Scheme.Modules.pullback i₂).obj L)
    (hagree : Scheme.Modules.pullbackSection (pullback.fst i₁ i₂) σ₁ ≫
        ((Scheme.Modules.pullbackComp (pullback.fst i₁ i₂) i₁).app L).hom ≫
          ((Scheme.Modules.pullbackCongr (pullback.condition (f := i₁) (g := i₂))).app L).hom =
      Scheme.Modules.pullbackSection (pullback.snd i₁ i₂) σ₂ ≫
        ((Scheme.Modules.pullbackComp (pullback.snd i₁ i₂) i₂).app L).hom) :
    ∃ σ : 𝟙_ X.Modules ⟶ L, Scheme.Modules.pullbackSection i₁ σ = σ₁ ∧ Scheme.Modules.pullbackSection i₂ σ = σ₂ ∧
      ∀ σ' : 𝟙_ X.Modules ⟶ L, Scheme.Modules.pullbackSection i₁ σ' = σ₁ → Scheme.Modules.pullbackSection i₂ σ' = σ₂ → σ' = σ := by sorry
