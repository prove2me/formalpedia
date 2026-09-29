-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_crossSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/cf0456d2-8a9f-56fb-897a-eced0dbc2cda
-- title:
--   Cross sections comparing two two-chart deformation representatives
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c : C \to \operatorname{Spec} R$ a morphism, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $A$ be an $R$-algebra and put $X' = C \times_{\operatorname{Spec} R} \operatorname{Spec} A$, with $X' \to \operatorname{Spec} A$ assumed separated. Let $\mathcal{W}$ and $\mathcal{W}'$ be two-affine open covers of $C$ (two affine opens with affine intersection whose union is $C$), and let $\delta$, $\delta'$ be maps from `RigKerDualNumber c ε A` — classes of rigidified line bundles on $C \times_{\operatorname{Spec} R} \operatorname{Spec} A[\epsilon]$ whose reduction along $A[\epsilon] \to A$ has trivial underlying bundle — to the two-chart Čech $H^1$ of the structure sheaf for the pullbacks to $X'$ of $\mathcal{W}$, resp. $\mathcal{W}'$, both assumed to be deformation-class maps: whenever frames $e_0$, $e_1$ on the two charts over $A[\epsilon]$ satisfy $e_1 = (1 + \epsilon f)e_0$ on the overlap, the class of the bundle is sent to the class of $f$. Let $x$ be such a class and $s \in \Gamma(X', W_0 \cap W_1)$, $s' \in \Gamma(X', V_0 \cap V_1)$ cocycles with $\delta(x) = [s]$, $\delta'(x) = [s']$, where $W_i$, $V_j$ are the pulled-back charts. Then there exist $g_{ij} \in \Gamma(X', W_i \cap V_j)$ for $i,j \in \{0,1\}$ such that, after restriction, $g_{00} = g_{10} + s$ on $(W_0 \cap W_1) \cap V_0$, $g_{01} = g_{11} + s$ on $(W_0 \cap W_1) \cap V_1$, $g_{01} = g_{00} + s'$ on $W_0 \cap (V_0 \cap V_1)$, and $g_{11} = g_{10} + s'$ on $W_1 \cap (V_0 \cap V_1)$.
--
--   This is the geometric half of the independence of the first-order deformation class of a rigidified line bundle from the chosen two-affine cover: the two Čech $1$-cocycles $s$ and $s'$ become cohomologous on the common refinement $\{W_i \cap V_j\}$, the $g_{ij}$ serving as the connecting $0$-cochain. It is used by [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers) to identify the images of the two classes in $H^1(X', \mathcal{O}_{X'})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace AlgebraicGeometry.RelPicard

theorem IsDeformationClassMap.exists_crossSections
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ  : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲}
    {δ' : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲'}
    (hδ : IsDeformationClassMap c ε A 𝒲 δ) (hδ' : IsDeformationClassMap c ε A 𝒲' δ')
    (x : RigKerDualNumber c ε A)
    (s  : ((𝒲.pullback c A).cover  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (s' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0;  let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0; let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom g00
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom s ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom g11
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom s ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom g00
          + (X'.presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom g11
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' := by sorry
