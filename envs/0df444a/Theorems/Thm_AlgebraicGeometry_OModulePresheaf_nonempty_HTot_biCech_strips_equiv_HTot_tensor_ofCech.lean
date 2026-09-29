-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/0fb7251b-2205-5fa3-b109-062265a3e9a7
-- title:
--   Cochain-level Künneth for bi-Čech complexes of box products
-- statement:
--   Let $k$ be a field and let $\pi_X\colon X\to\operatorname{Spec} k$ and $\pi_Y\colon Y\to\operatorname{Spec} k$ be separated morphisms of schemes. Let $F$ be a module on $X$ and $G$ a module on $Y$, each invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of the module along the inclusion $U\hookrightarrow$ the ambient scheme is isomorphic to the unit sheaf of modules of $U$. Let $\mathfrak U$ and $\mathfrak V$ be ordered affine covers of $X$ and $Y$ respectively, that is, families of opens indexed by a finite linearly ordered type, each open affine and the supremum of the family being the whole scheme, and let $n$ be a natural number. On the fibre product $X\times_k Y$, viewed over $k$ through the first projection followed by $\pi_X$, form the module $p_1^*F\otimes p_2^*G$ and the associated presheaf of $k$-modules of its sections, and take its bi-Čech double complex with respect to the two strip families $(p_1^{-1}\mathfrak U_i)_i$ and $(p_2^{-1}\mathfrak V_j)_j$ obtained as preimage families of $\mathfrak U$ and $\mathfrak V$. On the other side, form the bounded cochain complexes of $k$-modules given by the ordered Čech cochains of the sections presheaves of $F$ along $\mathfrak U$ and of $G$ along $\mathfrak V$ (their differentials squaring to zero by [`AlgebraicGeometry.OModulePresheaf.d_comp_d`](thm.html#AlgebraicGeometry.OModulePresheaf.d_comp_d)), and take their tensor double complex, with $(p,q)$ entry the tensor product over $k$ of the two levels, horizontal differential the right tensoring of the first differential and vertical differential the left tensoring of the second. The assertion is that the degree-$n$ total cohomology modules $\mathrm{HTot}$ of these two bounded double complexes, that is the quotients of the kernel of the signed total differential in degree $n$ by the image of the total differential from degree $n-1$ (by the zero submodule when $n=0$), are isomorphic as $k$-modules; the isomorphism is asserted only through nonemptiness of the type of such linear equivalences.
--
--   This is the cochain-level Künneth comparison underlying the computation of Čech cohomology of a box product of line bundles on $X\times_k Y$: the bi-Čech complex on the two strip families is levelwise identified with the tensor product of the two Čech complexes, because $p_1^{-1}U_s\cap p_2^{-1}V_t=U_s\times_k V_t$ is affine and its sections split as a tensor product. It feeds the finrank computation [`AlgebraicGeometry.OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G)
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) (n : ℕ) :
    Nonempty (DoubleComplex.HTot
        ((OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
          ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
            (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).biCech
          (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n ≃ₗ[k]
      DoubleComplex.HTot
        ((CochainCx.Bounded.ofCech (OModulePresheaf.ofModules πX F) 𝔘
            (AlgebraicGeometry.OModulePresheaf.d_comp_d (OModulePresheaf.ofModules πX F) 𝔘)).tensor
          (CochainCx.Bounded.ofCech (OModulePresheaf.ofModules πY G) 𝔙
            (AlgebraicGeometry.OModulePresheaf.d_comp_d (OModulePresheaf.ofModules πY G) 𝔙))) n) := by sorry
