-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IterCech_exists_mk_single_augTot_eq_mk_single_augCech_cup
-- name    : AlgebraicGeometry.OModulePresheaf.IterCech.exists_mk_single_augTot_eq_mk_single_augCech_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/99b046ca-6f4e-59f2-994c-21171070d416
-- title:
--   Augmented box product and cup product agree in Hⁿ
-- statement:
--   Fix a commutative ring $k$ and schemes $X$, $Y$ with structure morphisms $\pi_X : X \to \operatorname{Spec} k$ and $\pi_Y : Y \to \operatorname{Spec} k$, together with ordered affine covers $\mathfrak{U}$ of $X$ and $\mathfrak{V}$ of $Y$ (finite linearly ordered index sets $\mathfrak{U}.\iota$, $\mathfrak{V}.\iota$ with affine open members summing to $\top$). Write $P = X \times_{\operatorname{Spec} k} Y$ with projections $p_1 =$ `pullback.fst πX πY` and $p_2 =$ `pullback.snd πX πY`, and let $\mathfrak{A} = \mathfrak{U}.\mathrm{preimageFamily}(p_1)$, $\mathfrak{B} = \mathfrak{V}.\mathrm{preimageFamily}(p_2)$ be the ordered open families on $P$ with members $p_1^{-1}\mathfrak{U}.U_i$ and $p_2^{-1}\mathfrak{V}.U_j$. Two hypotheses make the pairwise intersections into an ordered affine cover: `haff` asserts that $\mathfrak{A}.U_i \sqcap \mathfrak{B}.U_j$ is affine open for all $i, j$, and `hcov` that $\bigsqcup_{(i,j)} \mathfrak{A}.U_i \sqcap \mathfrak{B}.U_j = \top$; the resulting cover $\mathfrak{P} = \mathfrak{A}.\mathrm{prodCover}\,\mathfrak{B}$ is indexed by the lexicographic product $\mathfrak{U}.\iota \times_{\mathrm{lex}} \mathfrak{V}.\iota$ with $\mathfrak{P}.U_{(i,j)} = \mathfrak{A}.U_i \sqcap \mathfrak{B}.U_j$. All cochain complexes are formed for the presheaf of sections `OModulePresheaf.unit` of the relevant structure morphism; on $P$ this is taken relative to $p_1$ followed by $\pi_X$. Write $E = (\mathrm{unit}(p_1 \gg \pi_X)).\mathrm{iterCech}\,\mathfrak{A}\,\mathfrak{B}\,\mathfrak{P}.\mathrm{toOpenFamily}$ for the associated bounded double complex, whose term in bidegree $(r, m)$ collects, for each $r$-simplex $K$ of $\mathfrak{P}$, the total degree-$m$ part of the bi-Čech complex of $\mathfrak{A}$ and of $\mathfrak{B}$ restricted to $\mathfrak{P}.\mathrm{inter}\,K$.
--
--   Fix $n \in \mathbb{N}$ and an index $i \in$ [`DoubleComplex.Diag n`](def/AlgebraicGeometry_DoubleComplex.html#L34), i.e. a pair $(p, q)$ of naturals with $p + q = n$. Let $\alpha$ lie in the kernel of the Čech differential of $\mathrm{unit}\,\pi_X$ for $\mathfrak{U}$ in degree $p$, and $\beta$ in the kernel of the Čech differential of $\mathrm{unit}\,\pi_Y$ for $\mathfrak{V}$ in degree $q$.
--
--   Two elements are built from this data. First, the external product: for a pair $st = (s, t)$ with $s$ a strictly monotone $(p+1)$-tuple in $\mathfrak{U}.\iota$ and $t$ a strictly monotone $(q+1)$-tuple in $\mathfrak{V}.\iota$, one takes $(p_1^{\#}\alpha(s))$, transported through the identification of $p_1^{-1}\bigsqcap_j \mathfrak{U}.U_{s(j)}$ with $\mathfrak{A}.\mathrm{inter}\,s$ and restricted to $\mathfrak{A}.\mathrm{inter}\,s \sqcap \mathfrak{B}.\mathrm{inter}\,t$, times the corresponding section obtained from $(p_2^{\#}\beta(t))$ by the analogous transport and restriction, the product being taken in the ring of sections over $\mathfrak{A}.\mathrm{inter}\,s \sqcap \mathfrak{B}.\mathrm{inter}\,t$. This defines an element of the bi-Čech term in bidegree $(p, q)$, and `Pi.single i` places it in the degree-$n$ total complex of the bi-Čech double complex of $\mathfrak{A}$ and $\mathfrak{B}$, all other diagonal components being zero. Second, the cup product on $\mathfrak{P}$ in degrees $p$ and $q$ with $p + q = n$ (witnessed by `i.2`), applied to the pullback cochains `unitPullback` of $\alpha$ along $p_1$ with index map $(i,j) \mapsto i$ and the inclusions $\mathfrak{P}.U_{(i,j)} \le \mathfrak{A}.U_i$, and of $\beta$ along $p_2$ with index map $(i,j) \mapsto j$ and the inclusions $\mathfrak{P}.U_{(i,j)} \le \mathfrak{B}.U_j$.
--
--   The two remaining hypotheses are cocycle conditions: `hbox` requires the above `Pi.single i` external product to lie in the kernel of [`DoubleComplex.dTot`](def/AlgebraicGeometry_DoubleComplex.html#L55) of the bi-Čech double complex of $\mathfrak{A}$ and $\mathfrak{B}$ in degree $n$, and `hcup` requires the above cup product to lie in the kernel of the Čech differential of $\mathrm{unit}(p_1 \gg \pi_X)$ for the cover $\mathfrak{P}$ in degree $n$.
--
--   The conclusion asserts the existence of two proofs $hz$ and $hw$, namely: that the element of the degree-$n$ total complex of $E$ whose only possibly nonzero component sits at the diagonal index $(0, n)$ and equals `IterCech.augTot` (restriction of a total bi-Čech cochain to the members $\mathfrak{P}.\mathrm{inter}\,K$) applied, in degree $n$, to the external product described above, lies in the kernel of [`DoubleComplex.dTot E n`](def/AlgebraicGeometry_DoubleComplex.html#L55); and that the element whose only possibly nonzero component sits at the diagonal index $(n, 0)$ and equals `IterCech.augCech` (restriction of a Čech cochain on $\mathfrak{P}$ into row zero of the iterated complex) applied, in degree $n$, to the cup product described above, likewise lies in that kernel. Moreover, with these witnesses the two corresponding classes in [`DoubleComplex.HTot E n`](def/AlgebraicGeometry_DoubleComplex.html#L65), the quotient of $\ker(\mathrm{dTot}\,E\,n)$ by the submodule `HTotB` (which is $\bot$ for $n = 0$ and the image of $\mathrm{dTot}\,E\,(n-1)$ otherwise), are equal.
--
--   This is the comparison step of the Künneth argument for Čech cohomology of the structure sheaf on a fibre product: in total cohomology of the iterated Čech double complex the augmented external product of two Čech cocycles and the augmented cup product of their pullbacks define one and the same class. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned), and rests on the degree-$n \ge 1$ zig-zag `IterCech.exists_dTot_eq_single_augTot_sub_single_augCech_cup` together with the exact degree-zero identity `IterCech.augTot_single_eq_augCech_cup_zero`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IterCech_exists_mk_single_augTot_eq_mk_single_augCech_cup.lean

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

theorem AlgebraicGeometry.OModulePresheaf.IterCech.exists_mk_single_augTot_eq_mk_single_augCech_cup
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)
    (n : ℕ) (i : DoubleComplex.Diag n)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
    (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2)))
    (hbox : (Pi.single i
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
                (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n)
      ∈ LinearMap.ker (DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech
          (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n))
    (hcup : ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 n i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1))
      ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d
          ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) n)) :
    ∃ (hz : Pi.single (M := fun rm : DoubleComplex.Diag n => (((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily)).C rm.1.1 rm.1.2) ⟨(0, n), by omega⟩
            (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily
            n
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
                (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n))
          ∈ LinearMap.ker (DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) n))
      (hw : Pi.single (M := fun rm : DoubleComplex.Diag n => (((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily)).C rm.1.1 rm.1.2) ⟨(n, 0), by omega⟩
            (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
            n
            ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 n i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1)))
          ∈ LinearMap.ker (DoubleComplex.dTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) n)),
      (Submodule.Quotient.mk ⟨_, hz⟩ : DoubleComplex.HTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).iterCech
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily) n) = Submodule.Quotient.mk ⟨_, hw⟩ := by sorry
