-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup
-- name    : AlgebraicGeometry.OModulePresheaf.IterCech.exists_dTot_eq_single_augTot_sub_single_augCech_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/6e06c4a8-ddd7-52e9-9675-6d97631133c4
-- title:
--   Product zig-zag in the iterated Čech complex
-- statement:
--   Let $k$ be a commutative ring, let $X,Y$ be schemes with structure morphisms $\pi_X : X \to \operatorname{Spec} k$, $\pi_Y : Y \to \operatorname{Spec} k$, and let $\mathfrak U$, $\mathfrak V$ be ordered affine covers of $X$ and $Y$ (finite linearly ordered index sets, affine opens with supremum $\top$). Write $P$ for the pullback of $\pi_X$ and $\pi_Y$, with projections $p_1,p_2$, and let $\mathfrak A = p_1^{-1}\mathfrak U$, $\mathfrak B = p_2^{-1}\mathfrak V$ be the induced ordered open families on $P$. Assume each $\mathfrak A_i \cap \mathfrak B_j$ is affine open (`haff`) and that these opens cover $P$ (`hcov`), so that `prodCover` yields the ordered affine cover $\mathfrak P$ of $P$ indexed by $\mathfrak U.\iota \times_{\mathrm{lex}} \mathfrak V.\iota$ with $\mathfrak P_{(i,j)} = \mathfrak A_i \cap \mathfrak B_j$, and its underlying open family. Let $m \in \mathbb N$, let $(p,q)$ be a point of [`DoubleComplex.Diag (m+1)`](def/AlgebraicGeometry_DoubleComplex.html#L34), i.e. $p+q = m+1$, and let $\alpha$ be a $p$-cocycle of the ordered Čech complex of $\mathcal O_X$ (the presheaf `unit` $\pi_X$) for $\mathfrak U$, and $\beta$ a $q$-cocycle of $\mathcal O_Y$ for $\mathfrak V$. Let $E$ be the iterated Čech double complex `iterCech` of $\mathcal{O}_P$ (the presheaf `unit` of $p_1$ followed by $\pi_X$) for the triple $(\mathfrak A, \mathfrak B, \mathfrak P)$. Then there exists $h \in \mathrm{Tot}^m E$ with $$d_{\mathrm{Tot}}^m h = \iota_{(0,m+1)}\bigl(\mathrm{augTot}(\alpha \boxtimes \beta)\bigr) - \iota_{(m+1,0)}\bigl(\mathrm{augCech}(p_1^{*}\alpha \cup p_2^{*}\beta)\bigr),$$ where $\iota_{(r,m+1-r)}$ denotes `Pi.single` at the indicated diagonal spot, $\alpha \boxtimes \beta$ is the element of $\mathrm{Tot}^{m+1}$ of the bi-Čech complex of $(\mathfrak A,\mathfrak B)$ concentrated in bidegree $(p,q)$ whose value at $(s,t)$ is the product of the restrictions of $p_1^{\sharp}(\alpha_s)$ and $p_2^{\sharp}(\beta_t)$ to $\mathfrak A\text{-}\mathrm{inter}(s) \cap \mathfrak B\text{-}\mathrm{inter}(t)$, and $p_1^{*}\alpha \cup p_2^{*}\beta$ is the `cup` product in degree $m+1$ on $\mathfrak P$ of the sorted pullbacks `unitPullback` of $\alpha$ along $p_1$ (index map the first lexicographic coordinate, with $\mathfrak P_{(i,j)} \le p_1^{-1}\mathfrak U_i$) and of $\beta$ along $p_2$ (second coordinate, $\mathfrak P_{(i,j)} \le p_2^{-1}\mathfrak V_j$); `augTot` and `augCech` are the restriction maps from $\mathrm{Tot}^{m+1}$ of the bi-Čech complex into $E^{0,m+1}$ and from Čech $(m+1)$-cochains on $\mathfrak P$ into $E^{m+1,0}$.
--
--   This is the positive-degree comparison of the two edge maps of the Čech triple complex on a product: the external product $\alpha \boxtimes \beta$, placed on the bi-Čech edge, and the cup product of the pullbacks of $\alpha$ and $\beta$ for the product cover, placed on the Čech edge, become cohomologous in the total complex of the iterated Čech double complex. It feeds the cohomology-class form of the statement, [`AlgebraicGeometry.OModulePresheaf.IterCech.exists_mk_single_augTot_eq_mk_single_augCech_cup`](thm.html#AlgebraicGeometry.OModulePresheaf.IterCech.exists_mk_single_augTot_eq_mk_single_augCech_cup), used in identifying the Künneth-type product on Čech cohomology of a fibre product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_IterCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.IterCech.exists_dTot_eq_single_augTot_sub_single_augCech_cup
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)
    (m : ℕ) (i : DoubleComplex.Diag (m + 1))
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
    (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2))) :
    ∃ h : DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) m,
      DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) m h =
        Pi.single (M := fun rm : DoubleComplex.Diag (m + 1) => (((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily)).C rm.1.1 rm.1.2) ⟨(0, m + 1), by omega⟩
          (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily
            (m + 1)
            (Pi.single i
              (fun st : 𝔘.Idx i.1.1 × 𝔙.Idx i.1.2 =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α.1 st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β.1 st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
                  (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) i.1.1 i.1.2) :
              DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech
                (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) (m + 1)))
        - Pi.single (M := fun rm : DoubleComplex.Diag (m + 1) => (((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily)).C rm.1.1 rm.1.2) ⟨(m + 1, 0), by omega⟩
          (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
            (m + 1)
            ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 (m + 1) i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1))) := by sorry
