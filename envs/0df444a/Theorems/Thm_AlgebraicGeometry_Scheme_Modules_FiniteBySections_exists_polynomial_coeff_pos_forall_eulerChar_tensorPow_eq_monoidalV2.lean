-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/e8eee171-05f6-53c9-8e0b-6bbee1bef3eb
-- title:
--   Positive d-th coefficient of the Hilbert polynomial of L
-- statement:
--   Let $k$ be a field, $X$ a scheme over $k$ with structure morphism $f \colon X \to \operatorname{Spec} k$, and assume $X$ is integral. Let $d$ be a natural number with $\operatorname{topologicalKrullDim} X = d$. Let $\mathcal L$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of $\mathcal L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of rings of $U$, and assume $\mathcal L$ is finite by sections over $f$: there are $N$ and global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L, \top)$ together with a morphism $\varphi \colon X \to \operatorname{Proj} k[X_0,\dots,X_N]$ satisfying $\varphi$ followed by the projection to $\operatorname{Spec} k$ equals $f$, such that on every open $V$ contained in $\varphi^{-1}$ of the standard chart $D(X_i)$ the map $g \mapsto g \cdot \sigma_i|_V$ from $\Gamma(X,V)$ to $\Gamma(\mathcal L,V)$ is bijective, and such that on $\varphi^{-1} D(X_i)$ the pullback of the ratio $X_j/X_i$ carries $\sigma_i$ to $\sigma_j$; and $\varphi$ is a finite morphism. Let $\mathcal K$ be an ordered affine cover of $X$, that is, a finite linearly ordered index type together with affine opens whose supremum is $\top$. Then there is a polynomial $q \in \mathbb Q[T]$ whose coefficient of $T^d$ is strictly positive such that for every natural number $m$ the Euler characteristic $\sum_{i} (-1)^i \dim_k \check H^i(\mathcal K, \cdot)$ of the $k$-module presheaf of sections of the $m$-th tensor power $\mathcal L^{\otimes m}$ (with $\mathcal L^{\otimes 0}$ the unit object, $\mathcal L^{\otimes (n+1)} = \mathcal L^{\otimes n} \otimes \mathcal L$) on $\mathcal K$ equals $q(m)$. Note that the conclusion asserts only positivity of the coefficient of $T^d$, with no upper bound on $\deg q$.
--
--   This is the Hilbert-polynomial statement for an invertible sheaf defining a finite morphism to projective space over a field: the Čech Euler characteristics $\chi(\mathcal L^{\otimes m})$ are the values at natural numbers of a single rational polynomial whose coefficient in degree $d = \dim X$ is positive, so that $\chi(\mathcal L^{\otimes m})$ grows like a positive multiple of $m^d$. It is used in the treatment of polarisations, for the finiteness of the kernel points and the positivity of the geometric fibrewise $H^0$-rank attached to a polarisation, and in showing that a suitable tensor power of a line bundle in the relative Picard kernel fails to be trivial after pullback along a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq_monoidalV2.lean

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

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq_monoidalV2
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X]
    (d : ℕ) (hd : topologicalKrullDim X = d)
    (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hfs : 𝓛.FiniteBySections f)
    (𝒦 : X.OrderedAffineCover) :
    ∃ q : Polynomial ℚ, 0 < q.coeff d ∧
      ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) := by sorry
