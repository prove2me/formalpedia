-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/9052b415-b8f5-53b1-a4b9-cb4dffc19fc8
-- title:
--   Global sections of powers of an ample sheaf grow like nᵈ
-- statement:
--   Let $k$ be a field, let $X$ be an integral scheme with a morphism $f\colon X\to\operatorname{Spec} k$, and let $d$ be a natural number with $d\le\operatorname{topologicalKrullDim} X$ in $\mathbb{N}\infty$ with a bottom element. Let $\mathcal{L}$ be an $\mathcal{O}_X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback of $\mathcal{L}$ along $U\hookrightarrow X$ is isomorphic to the unit sheaf of modules, and let $\mathfrak{P}$ be a `ProjPresentation` of $\mathcal{L}$ over $f$ of size $N$: global sections $\sigma_0,\dots,\sigma_N\in\Gamma(\mathcal{L},\top)$ together with a morphism $\varphi=\mathfrak{P}.\mathrm{toProj}\colon X\to\operatorname{Proj} k[x_0,\dots,x_N]$ over $\operatorname{Spec} k$ such that on every open $V$ contained in $\varphi^{-1}D_+(x_i)$ multiplication by the restriction of $\sigma_i$ is a bijection $\Gamma(X,V)\to\Gamma(\mathcal{L},V)$, and such that over $\varphi^{-1}D_+(x_i)$ the pullback of $x_j/x_i$ carries $\sigma_i$ to $\sigma_j$. Assume $\varphi$ is finite. Then there is a rational number $c>0$ such that for every $n\in\mathbb{N}$ and every ordered affine cover $\mathcal{K}$ of $X$ (a finite linearly ordered family of affine opens with supremum $\top$), $c\,n^{d}$ is at most the $k$-dimension of the degree-zero Čech cohomology of the presheaf $U\mapsto\Gamma(\mathcal{L}^{\otimes n},U)$ with respect to $\mathcal{K}$, where $\mathcal{L}^{\otimes n}$ is the $n$-fold tensor power defined by $\mathcal{L}^{\otimes 0}=\mathbf{1}$ and $\mathcal{L}^{\otimes (n+1)}=\mathcal{L}^{\otimes n}\otimes\mathcal{L}$.
--
--   This is the elementary half of the assertion that on a $d$-dimensional integral variety the Hilbert function of an ample invertible sheaf grows exactly like $n^d$, i.e. that an ample invertible sheaf is big; the bound is uniform in the chosen ordered affine cover, the degree-zero Čech group being canonically $\Gamma(X,\mathcal{L}^{\otimes n})$. It is used in the proof that the Euler characteristics $\chi(\mathcal{L}^{\otimes n})$ are given by a polynomial in $n$ whose leading coefficient is positive.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsIntegral X]
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X)
    {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N)
    (hfin : IsFinite 𝔓.toProj) :
    ∃ c : ℚ, 0 < c ∧ ∀ (n : ℕ) (𝒦 : X.OrderedAffineCover),
      c * (n : ℚ) ^ d ≤ ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 : ℚ) := by sorry
