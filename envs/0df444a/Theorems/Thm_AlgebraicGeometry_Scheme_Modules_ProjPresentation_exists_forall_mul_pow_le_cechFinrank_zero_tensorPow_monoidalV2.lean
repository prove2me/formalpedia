-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ea7f6a2c-bef2-5fc3-9d1b-5ec86e16a31b
-- title:
--   Invertible sheaf with finite Proj presentation: c nᵈ ≤ h⁰(L^{⊗ n})
-- statement:
--   Let $k$ be a field, let $X$ be an integral scheme equipped with a morphism $f \colon X \to \operatorname{Spec} k$, and let $d$ be a natural number with $d \le \operatorname{topologicalKrullDim} X$ (as elements of $\mathrm{WithBot}\,\mathbb N_\infty$). Let $\mathcal L$ be an $X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback of $\mathcal L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $\mathfrak P$ be a `ProjPresentation` of $\mathcal L$ over $f$ of size $N$: global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L, \top)$ together with a morphism $\varphi = \mathfrak P.\mathrm{toProj} \colon X \to \operatorname{Proj}$ of the graded algebra of homogeneous polynomials in $N+1$ variables over $k$ such that $\varphi$ followed by the structure map $\operatorname{Proj} \to \operatorname{Spec} k$ is $f$; such that on every open $V$ contained in $\varphi^{-1}D_+(X_i)$ the map $g \mapsto g \cdot \sigma_i|_V$ from $\Gamma(X,V)$ to $\Gamma(\mathcal L,V)$ is bijective; and such that for all $i,j$ the pullback along $\varphi$ of the ratio $X_j/X_i$ on $D_+(X_i)$ multiplies $\sigma_i|_{\varphi^{-1}D_+(X_i)}$ into $\sigma_j|_{\varphi^{-1}D_+(X_i)}$. Assume moreover that $\varphi$ is a finite morphism. Then there is a rational number $c > 0$ such that for every natural number $n$ and every ordered affine cover $\mathcal K$ of $X$ (a finite linearly ordered family of affine opens with supremum $\top$) one has $c\,n^{d} \le \dim_k H^0$ of the Čech complex of $\mathcal K$ with values in the presheaf of sections of the $n$-th tensor power $\mathcal L^{\otimes n}$ (defined by $\mathcal L^{\otimes 0} = \mathbf 1$, $\mathcal L^{\otimes (m+1)} = \mathcal L^{\otimes m} \otimes \mathcal L$), the inequality being read in $\mathbb Q$.
--
--   This is the elementary half of the statement that the Hilbert polynomial of an ample invertible sheaf on a $d$-dimensional variety has degree $d$ — in the language of positivity, that an ample invertible sheaf is big. It feeds the construction of the Euler-characteristic polynomial of the powers $\mathcal L^{\otimes n}$ with positive leading coefficient, namely [`AlgebraicGeometry.Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq_monoidalV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsIntegral X]
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X)
    {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N)
    (hfin : IsFinite 𝔓.toProj) :
    ∃ c : ℚ, 0 < c ∧ ∀ (n : ℕ) (𝒦 : X.OrderedAffineCover),
      c * (n : ℚ) ^ d ≤ ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 : ℚ) := by sorry
