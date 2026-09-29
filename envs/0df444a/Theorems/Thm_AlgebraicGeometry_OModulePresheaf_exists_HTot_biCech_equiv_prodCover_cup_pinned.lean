-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HTot_biCech_equiv_prodCover_cup_pinned
-- name    : AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/0a2c64f0-ec1a-5ef7-884d-ce593985ce58
-- title:
--   Künneth comparison for the box cover, pinned on cup products
-- statement:
--   Let $k$ be a field and let $\pi_X : X \to \operatorname{Spec} k$, $\pi_Y : Y \to \operatorname{Spec} k$ be separated morphisms of schemes, write $P$ for the fibre product $X \times_{\operatorname{Spec} k} Y$ with projections $p_1, p_2$, and let $\mathfrak U$, $\mathfrak V$ be ordered affine covers of $X$ and $Y$ (finite linearly ordered index sets with affine opens whose supremum is $\top$). Put $\mathfrak A_i = p_1^{-1} U_i$ and $\mathfrak B_j = p_2^{-1} V_j$, and assume that each $\mathfrak A_i \sqcap \mathfrak B_j$ is an affine open (hypothesis `haff`) and that $\bigsqcup_{i,j} \mathfrak A_i \sqcap \mathfrak B_j = \top$ (hypothesis `hcov`); these data yield the ordered affine cover $\mathfrak P$ of $P$ indexed by the lexicographic product of the two index sets, with opens $\mathfrak A_i \sqcap \mathfrak B_j$. The assertion is the existence of a family of $k$-linear isomorphisms $\theta_n$, for all $n$, from the $n$-th total cohomology of the bi-Čech double complex of the structure presheaf $U \mapsto \Gamma(P, U)$ (the `unit` of $p_1$ followed by $\pi_X$) with respect to $(\mathfrak A, \mathfrak B)$ — that is, $\ker d_{\mathrm{Tot}}^n$ modulo $0$ for $n = 0$ and modulo the image of $d_{\mathrm{Tot}}^{n-1}$ otherwise — to the $n$-th cohomology of the ordered Čech complex of that presheaf for the cover $\mathfrak P$, subject to the following pinning. For every $n$, every pair $(p,q)$ with $p + q = n$, every $\alpha$ in the kernel of the $p$-th Čech differential of $\mathcal O_X$ for $\mathfrak U$ and every $\beta$ in the kernel of the $q$-th Čech differential of $\mathcal O_Y$ for $\mathfrak V$, the total cochain concentrated in bidegree $(p,q)$ whose value at a pair of strictly monotone indices $(s,t)$ is the product, in $\Gamma(P, \bigsqcap_j \mathfrak A_{s(j)} \sqcap \bigsqcap_j \mathfrak B_{t(j)})$, of the restrictions of $p_1^{\#}(\alpha_s)$ and $p_2^{\#}(\beta_t)$, is a total cocycle; the cup product on $\mathfrak P$ of the pullback cochain `unitPullback` of $\alpha$ along $p_1$ (index map the first lexicographic projection) with the pullback of $\beta$ along $p_2$ (second projection) is a Čech cocycle; and $\theta_n$ sends the class of the former to the class of the latter. Both cocycle statements are part of the conclusion.
--
--   This is the Cartan–Leray comparison between the total cohomology of the bi-Čech double complex of the two strip families on $X \times_k Y$ and the Čech cohomology of the box cover $\mathfrak P$, in the form in which the isomorphism is pinned down on external products of cocycles: classes of boxes go to classes of cup products of the pulled-back cochains. It is used in the proof of the injectivity on the diagonal of the Künneth map for the structure sheaf, `kunneth_toModule_diag_injective_of_cls_unitPullback`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_HTot_biCech_equiv_prodCover_cup_pinned.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤) :
    ∃ θ : ∀ n : ℕ,
        DoubleComplex.HTot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n ≃ₗ[k]
          (CochainCx.Bounded.ofCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)).H n,

      ∀ (n : ℕ) (i : DoubleComplex.Diag n)
        (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
        (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2))),
        ∃ (hz : (Pi.single i
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
                (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n) ∈
            LinearMap.ker (DoubleComplex.dTot _ n))
          (hw : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 n i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1) ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) n)),
          θ n (Submodule.Quotient.mk ⟨_, hz⟩) = Submodule.Quotient.mk ⟨_, hw⟩ := by sorry
