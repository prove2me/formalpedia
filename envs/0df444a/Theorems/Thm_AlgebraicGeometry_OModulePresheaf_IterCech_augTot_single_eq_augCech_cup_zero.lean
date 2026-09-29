-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IterCech_augTot_single_eq_augCech_cup_zero
-- name    : AlgebraicGeometry.OModulePresheaf.IterCech.augTot_single_eq_augCech_cup_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f241f1c7-7fda-552d-98dc-3b09c7edc5a2
-- title:
--   Degree zero: augmented external product equals augmented cup product
-- statement:
--   Let $k$ be a commutative ring, let $\pi_X : X \to \operatorname{Spec} k$ and $\pi_Y : Y \to \operatorname{Spec} k$ be schemes over $k$, and let $\mathfrak U$, $\mathfrak V$ be ordered affine covers of $X$ and of $Y$ (finite linearly ordered index sets with affine open members covering the space). On the fibre product $P = X \times_{\operatorname{Spec} k} Y$ with projections $p_1 =$ `pullback.fst` and $p_2 =$ `pullback.snd`, form the preimage families $p_1^{-1}\mathfrak U$ and $p_2^{-1}\mathfrak V$. Assume each $p_1^{-1}U_i \cap p_2^{-1}V_j$ is affine open (`haff`) and that these opens have supremum $\top$ (`hcov`), so that `prodCover` is an ordered affine cover of $P$ indexed by the lexicographic product of the two index sets. Let $i$ be an element of [`DoubleComplex.Diag 0`](def/AlgebraicGeometry_DoubleComplex.html#L34), that is a pair $(p,q)$ of naturals together with a proof that $p + q = 0$, and let $\alpha$, $\beta$ be cocycles, i.e. elements of the kernels of the Čech differentials in degrees $p$ and $q$ of the structure-sheaf presheaf `unit` on $\mathfrak U$ and on $\mathfrak V$ respectively. The conclusion is an equality of two elements of the group $C$ in bidegree $(0,0)$ attached to `unit` $(p_1 \circ \pi_X$ viewed in diagrammatic order as $p_1 \ggg \pi_X)$, the two families $p_1^{-1}\mathfrak U$, $p_2^{-1}\mathfrak V$ and the open family underlying `prodCover`. On the left, `augTot` in total degree $0$ — the map restricting each component of a total cochain to the intersections $\mathfrak C.\mathrm{inter}\,K$ of the cover `prodCover` — is applied to the total cochain concentrated at the index $i$ (via `Pi.single`) whose value sends a pair $(s,t)$ of strictly monotone tuples to the product, inside $\Gamma$ of $\bigcap_j p_1^{-1}U_{s_j} \cap \bigcap_j p_2^{-1}V_{t_j}$, of the restrictions of $p_1^\sharp(\alpha(s))$ and $p_2^\sharp(\beta(t))$, using the identification of the preimage of a finite intersection with the intersection of the preimages. On the right, `augCech` in degree $0$ — restriction of a Čech cochain on `prodCover` along the inclusions of these intersections — is applied to the cup product in degrees $(p,q,0)$, using the proof $p+q=0$, of the pullback cochains `unitPullback` of $\alpha$ along $p_1$ and of $\beta$ along $p_2$, taken with respect to the index maps sending a lexicographic pair to its first, respectively second, component, and the inclusions $p_1^{-1}U_i \cap p_2^{-1}V_j \le p_1^{-1}U_i$, respectively $\le p_2^{-1}V_j$.
--
--   This is the degree-$(0,0)$ comparison in the product zig-zag for Čech cochains on a fibre product: in total degree $0$ the row augmentation of the external product $\alpha \boxtimes \beta$ agrees exactly, with no correcting homotopy, with the column augmentation of the cup product of the pulled-back cocycles $p_1^*\alpha$ and $p_2^*\beta$. It is the base case used by [`AlgebraicGeometry.OModulePresheaf.IterCech.exists_mk_single_augTot_eq_mk_single_augCech_cup`](thm.html#AlgebraicGeometry.OModulePresheaf.IterCech.exists_mk_single_augTot_eq_mk_single_augCech_cup), where the two augmentations of the bi-Čech double complex are identified in cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IterCech_augTot_single_eq_augCech_cup_zero.lean

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

theorem AlgebraicGeometry.OModulePresheaf.IterCech.augTot_single_eq_augCech_cup_zero
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)
    (i : DoubleComplex.Diag 0)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
    (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2))) :
    (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily
            0
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
                (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) 0))
      = (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
            0
            ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 0 i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1))) := by sorry
