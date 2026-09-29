-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_eq_zero_of_iso_tensor_pullback_of_H0_eq_bot_of_subsingleton_HSucc
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinrank_eq_zero_of_iso_tensor_pullback_of_H0_eq_bot_of_subsingleton_HSucc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/b1b010b1-8bce-5510-9862-2d80e8042b24
-- title:
--   Vanishing of Čech ranks from a Künneth absorption isomorphism
-- statement:
--   Let $k$ be a field and let $X$, $Y$ be schemes (in the lowest universe) equipped with proper morphisms $\pi_X : X \to \operatorname{Spec} k$ and $\pi_Y : Y \to \operatorname{Spec} k$. Let $F$ be a module on $X$ and $N$ a module on $Y$, both invertible in the sense that every point has an open neighbourhood $U$ over which the pullback along $U \hookrightarrow X$ (resp. $Y$) is isomorphic to the unit module of $U$. Let $\mathfrak V$ be an ordered affine cover of $Y$, i.e. a finite linearly ordered family of affine opens whose supremum is $\top$, and assume that for the ordered Čech complex of the presheaf of sections of $N$, regarded with its $k$-module structures through $\pi_Y$, the degree-zero cohomology $\ker d^0$ is the zero submodule and each higher group $\ker d^{i+1}/\operatorname{im} d^i$ is a subsingleton; assume also that the degree-zero Čech rank $\operatorname{finrank}_k \ker d^0$ of the unit module of $Y$ with respect to $\mathfrak V$ is positive. Let $\Phi$ be a self-isomorphism of the fibre product $X \times_{\operatorname{Spec} k} Y$ with $\Phi \text{ followed by } p_1 \text{ followed by } \pi_X = p_1 \text{ followed by } \pi_X$, and suppose there exists an isomorphism of modules $(\Phi \text{ followed by } p_1)^* F \cong p_1^* F \otimes p_2^* N$. Then for every ordered affine cover $\mathfrak U$ of $X$ and every $n \in \mathbb N$ the $n$-th Čech rank of $F$ over $\mathfrak U$ vanishes: the $k$-dimension of $\ker d^0$ for $n = 0$, and of $\ker d^{n}/\operatorname{im} d^{n-1}$ for $n > 0$, is $0$.
--
--   This is the absorption step in the Künneth-style argument: an invertible sheaf on a proper $k$-scheme whose pullback to a product becomes, after an automorphism of the product compatible with the first projection, a twist by an acyclic invertible sheaf on the second factor has all Čech cohomology of rank zero. It is used in the study of polarisations, where it feeds the vanishing criterion [`AlgebraicGeometry.Polarisation.cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit`](thm.html#AlgebraicGeometry.Polarisation.cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_eq_zero_of_iso_tensor_pullback_of_H0_eq_bot_of_subsingleton_HSucc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinrank_eq_zero_of_iso_tensor_pullback_of_H0_eq_bot_of_subsingleton_HSucc
    {k : Type} [Field k] {X Y : Scheme.{0}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsProper πX] [IsProper πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (N : Y.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝔙 : Y.OrderedAffineCover)
    (hN0 : (OModulePresheaf.ofModules πY N).H0 𝔙 = ⊥ ∧ ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules πY N).HSucc 𝔙 i))
    (hY0 : 0 < (OModulePresheaf.ofModules πY (𝟙_ Y.Modules)).cechFinrank 𝔙 0)
    (Φ : pullback πX πY ≅ pullback πX πY)
    (hΦ : Φ.hom ≫ pullback.fst πX πY ≫ πX = pullback.fst πX πY ≫ πX)
    (e : Nonempty ((Scheme.Modules.pullback (Φ.hom ≫ pullback.fst πX πY)).obj F ≅
      (Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗ (Scheme.Modules.pullback (pullback.snd πX πY)).obj N))
    (𝔘 : X.OrderedAffineCover) (n : ℕ) :
    (OModulePresheaf.ofModules πX F).cechFinrank 𝔘 n = 0 := by sorry
