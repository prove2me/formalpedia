-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
-- name    : AlgebraicGeometry.RelPicard.exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/05d5f183-b419-5328-b357-b0f9f60be84f
-- title:
--   Two frame cocycles on two covers are cohomologous after cross refinement
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme with a morphism $c \colon C \to \operatorname{Spec} R$, and $A$ a commutative $R$-algebra such that the projection $\operatorname{pr}_2 \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} A \to \operatorname{Spec} A$ is separated. Let $\mathcal{W}$, $\mathcal{W}'$ be two-affine open covers of $C$ (each given by two affine opens with affine intersection whose union is $C$), and let $N$ be a sheaf of modules on $X'' = C \times_{\operatorname{Spec} R} \operatorname{Spec} A[\varepsilon]$. Assume given $e_0 \in \Gamma(N, W_0^{\varepsilon})$ and $e_1 \in \Gamma(N, W_1^{\varepsilon})$ over the pullbacks to $X''$ of the two opens of $\mathcal{W}$, each a frame in the sense that for every open $W$ contained in the relevant open the map $h \mapsto h \cdot (e_i|_W)$ from $\Gamma(X'', W)$ to $\Gamma(N, W)$ is bijective; similarly $e_0', e_1'$ for $\mathcal{W}'$. Assume further that on $W_0^{\varepsilon} \cap W_1^{\varepsilon}$ one has $e_1 = (1 + \varepsilon \, \iota g) \cdot e_0$, where $g$ is a section of the structure sheaf of $X' = C \times_{\operatorname{Spec} R} \operatorname{Spec} A$ over $W_0 \cap W_1$ and $\iota$ denotes pullback of functions along the thickening $X' \to X''$, and correspondingly $e_1' = (1 + \varepsilon \, \iota g') \cdot e_0'$ on $V_0^{\varepsilon} \cap V_1^{\varepsilon}$ with $g' \in \Gamma(X', V_0 \cap V_1)$. Then there exist sections $g_{ij} \in \Gamma(X', W_i \cap V_j)$ for $i,j \in \{0,1\}$ such that, after restriction, $g_{0j} = g_{1j} + g$ on $(W_0 \cap W_1) \cap V_j$ for $j = 0,1$, and $g_{i1} = g_{i0} + g'$ on $W_i \cap (V_0 \cap V_1)$ for $i = 0,1$.
--
--   This is the cover-change (refinement) step, at the level of Čech cochains, for the $1$-cocycles of the structure sheaf attached to a first-order deformation of a line bundle: the cocycles $g$ and $g'$ read off from frames on two different two-chart covers become cohomologous on the four-chart cross refinement $\{W_i \cap V_j\}$, with $(g_{ij})$ as connecting $0$-cochain. It rests on the unique splitting of sections over the dual-number thickening of an affine open, and is used in the comparison of Čech $H^1$ classes for the deformation-class map attached to a module over the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace AlgebraicGeometry.RelPicard

theorem exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    (N : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Modules)
    (e₀ : Γ(N, (𝒲.pullback c (DualNumber A)).U0)) (e₁ : Γ(N, (𝒲.pullback c (DualNumber A)).U1))
    (g : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (h₀ : Scheme.Modules.IsFrameOn e₀ (𝒲.pullback c (DualNumber A)).U0)
    (h₁ : Scheme.Modules.IsFrameOn e₁ (𝒲.pullback c (DualNumber A)).U1)
    (hg : N.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒲 c g) •
        N.presheaf.map (homOfLE inf_le_left).op e₀)
    (e₀' : Γ(N, (𝒲'.pullback c (DualNumber A)).U0)) (e₁' : Γ(N, (𝒲'.pullback c (DualNumber A)).U1))
    (g' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (h₀' : Scheme.Modules.IsFrameOn e₀' (𝒲'.pullback c (DualNumber A)).U0)
    (h₁' : Scheme.Modules.IsFrameOn e₁' (𝒲'.pullback c (DualNumber A)).U1)
    (hg' : N.presheaf.map (homOfLE inf_le_right).op e₁' =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒲' c g') •
        N.presheaf.map (homOfLE inf_le_left).op e₀') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0;  let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0; let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom g00
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom g ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom g11
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom g ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom g00
          + (X'.presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom g' ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom g11
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom g' := by sorry
