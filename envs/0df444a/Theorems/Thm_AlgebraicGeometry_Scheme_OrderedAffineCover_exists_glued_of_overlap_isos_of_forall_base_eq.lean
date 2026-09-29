-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_glued_of_overlap_isos_of_forall_base_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/c9a61132-9e69-5889-845c-36bdd1453e72
-- title:
--   Gluing an ordered affine cover along point-fixing overlap automorphisms
-- statement:
--   Let $p \colon X_0 \to S$ be a morphism of schemes and let $\mathcal U$ be an ordered affine cover of $X_0$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq X_0$, each affine, whose supremum is $\top$. For $i \in \mathbb N$ the set $\mathcal U.\mathrm{Idx}\,i$ consists of the strictly monotone maps $s \colon \mathrm{Fin}(i+1) \to \iota$, and $\mathcal U.\mathrm{inter}\,s = \bigsqcap_j U_{s(j)}$, while $\mathcal U.\mathrm{face}\,r\,j$ deletes the $j$-th entry of $r$. Assume given, for each $s \in \mathcal U.\mathrm{Idx}\,1$ (i.e. each pair $s(0) < s(1)$), an isomorphism $\tau_s$ of the open subscheme $\mathcal U.\mathrm{inter}\,s$ with itself such that $\tau_s$ followed by the inclusion of $\mathcal U.\mathrm{inter}\,s$ into $X_0$ and then $p$ equals the inclusion followed by $p$, and such that $\tau_s$ is the identity on underlying points. Assume further that for each $r \in \mathcal U.\mathrm{Idx}\,2$ there are endomorphisms $\rho_0,\rho_1,\rho_2$ of the triple overlap $\mathcal U.\mathrm{inter}\,r$ with $\rho_j$ followed by the inclusion $\mathcal U.\mathrm{inter}\,r \subseteq \mathcal U.\mathrm{inter}(\mathcal U.\mathrm{face}\,r\,j)$ equal to that inclusion followed by $\tau_{\mathcal U.\mathrm{face}\,r\,j}$, and with $\rho_1 = \rho_2$ followed by $\rho_0$. Then there exist a scheme $X$, a morphism $f_X \colon X \to S$ and morphisms $\iota_i \colon U_i \to X$ such that each $\iota_i$ is an open immersion; $\iota_i$ followed by $f_X$ equals the inclusion $U_i \subseteq X_0$ followed by $p$; every point of $X$ is in the image of some $\iota_i$; for each pair $s(0)<s(1)$ the inclusion $\mathcal U.\mathrm{inter}\,s \subseteq U_{s(0)}$ followed by $\iota_{s(0)}$ equals $\tau_s$ followed by the inclusion $\mathcal U.\mathrm{inter}\,s \subseteq U_{s(1)}$ and then $\iota_{s(1)}$; and for all $i,j$ and points $y \in U_i$, $y' \in U_j$ one has $\iota_i(y) = \iota_j(y')$ in $X$ if and only if $y$ and $y'$ have the same image in $X_0$.
--
--   This is the gluing construction for schemes (EGA I 2.4.1) in the special case of transition data given by automorphisms of the honest overlaps inside an ambient scheme $X_0$ which act trivially on points, so that the resulting glued scheme has the same underlying point set as $X_0$ while the structure morphism to $S$ is respected. It is used in the construction of deformations of Jacobians with good reduction, through [`GoodReductionJacobian.BareDeformation.exists_glued_scheme_of_overlap_isos`](thm.html#GoodReductionJacobian.BareDeformation.exists_glued_scheme_of_overlap_isos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_glued_of_overlap_isos_of_forall_base_eq
    {X₀ S : Scheme.{0}} (p : X₀ ⟶ S) (𝒰 : X₀.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτS : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ p = (𝒰.inter s).ι ≫ p)
    (hτpt : ∀ (s : 𝒰.Idx 1) (x : ↑(𝒰.inter s)), (τ s).hom.base x = x)
    (hcoc : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ X₀.homOfLE (𝒰.inter_le_inter_face r j)
            = X₀.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) :
    ∃ (X : Scheme.{0}) (fX : X ⟶ S) (ιU : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ X),
      (∀ i, IsOpenImmersion (ιU i)) ∧
      (∀ i, ιU i ≫ fX = (𝒰.U i).ι ≫ p) ∧
      (∀ x : X, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιU i).base y = x) ∧
      (∀ s : 𝒰.Idx 1,
        X₀.homOfLE (𝒰.inter_le s 0) ≫ ιU (s.1 0) = (τ s).hom ≫ X₀.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1)) ∧
      (∀ (i j : 𝒰.ι) (y : ↑(𝒰.U i)) (y' : ↑(𝒰.U j)),
        (ιU i).base y = (ιU j).base y' ↔ (𝒰.U i).ι.base y = (𝒰.U j).ι.base y') := by sorry
