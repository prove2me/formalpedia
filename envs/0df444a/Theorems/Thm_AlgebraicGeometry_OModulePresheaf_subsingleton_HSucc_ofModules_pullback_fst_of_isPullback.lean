-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_ofModules_pullback_fst_of_isPullback
-- name    : AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_ofModules_pullback_fst_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/67e729b3-b577-56e4-a32b-ee0a9da91c91
-- title:
--   Čech vanishing transported to the chosen fibre product
-- statement:
--   Let $R$ and $k$ be commutative rings, let $X$ and $X_k$ be schemes, let $f\colon X\to\operatorname{Spec}R$ be a separated morphism, let $\tau\colon\operatorname{Spec}k\to\operatorname{Spec}R$ be a morphism, and let $g_k\colon X_k\to X$, $f_k\colon X_k\to\operatorname{Spec}k$ form a cartesian square: $g_k$ followed by $f$ equals $f_k$ followed by $\tau$, the square being a pullback square. Let $M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the restriction $(\,\cdot\,)|_U$ of $M$ along $U\hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$, and let $j$ be a natural number. Assume that for every ordered affine cover of $X_k$ — a finite linearly ordered index set together with affine opens whose supremum is $\top$ — the module $\mathrm{HSucc}$ at index $j$ of the $\mathcal{O}$-module presheaf $\mathrm{ofModules}\,f_k\,(g_k^*M)$, namely the quotient of $\ker d^{j+1}$ by the part of $\operatorname{im} d^{j}$ lying in it, is a subsingleton; here $\mathrm{ofModules}\,\pi\,N$ sends an open $U$ to the sections $\Gamma(N,U)$ with their module structure over the base ring induced by $\pi$ and with the restriction maps of $N$. Then for every ordered affine cover $\mathcal{W}$ of the chosen fibre product $\mathrm{pullback}\,f\,\tau$, the corresponding module $\mathrm{HSucc}$ at index $j$ of $\mathrm{ofModules}$ of the second projection applied to the pullback of $M$ along the first projection is a subsingleton.
--
--   This is the transport statement saying that vanishing of the $(j+1)$-st ordered Čech cohomology of the pulled-back invertible module, assumed for all ordered affine covers of an arbitrary fibre product of $X$ and $\operatorname{Spec}k$ over $\operatorname{Spec}R$, holds for covers of Mathlib's chosen fibre product $\mathrm{pullback}\,f\,\tau$. It feeds the section-lifting result [`AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc), where the Čech-vanishing hypothesis must be available for the canonical base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_ofModules_pullback_fst_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_ofModules_pullback_fst_of_isPullback
    {R k : Type u} [CommRing R] [CommRing k] {X Xk : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (τ : Spec (.of k) ⟶ Spec (.of R)) (fk : Xk ⟶ Spec (.of k)) (gk : Xk ⟶ X) (hgk : IsPullback gk fk f τ)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (j : ℕ)
    (hvan : ∀ 𝒰 : Xk.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules fk ((Scheme.Modules.pullback gk).obj M)).HSucc 𝒰 j))
    (𝒲 : (pullback f τ).OrderedAffineCover) :
    Subsingleton ((OModulePresheaf.ofModules (pullback.snd f τ)
      ((Scheme.Modules.pullback (pullback.fst f τ)).obj M)).HSucc 𝒲 j) := by sorry
