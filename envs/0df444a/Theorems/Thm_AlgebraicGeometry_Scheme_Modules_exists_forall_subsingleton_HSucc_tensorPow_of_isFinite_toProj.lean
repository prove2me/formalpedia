-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
-- name    : AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/6d9deedb-0b1f-5a74-8061-e291e32ad92b
-- title:
--   Degree-one Čech vanishing for high tensor powers of L
-- statement:
--   Let $k$ be a field, let $X$ be a scheme with a morphism $f\colon X\to\operatorname{Spec} k$, and let $L$ be an $\mathcal O_X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module of $U$. Let $N$ be a natural number and let $\mathfrak P$ be a projective presentation of $L$ relative to $f$ of size $N$: it consists of global sections $\sigma_i\in\Gamma(L,\top)$ indexed by $i\in\mathrm{Fin}(N+1)$, a morphism $\varphi=\mathfrak P.\mathrm{toProj}\colon X\to\operatorname{Proj}$ of the ring of homogeneous polynomials in $N+1$ variables over $k$ whose composite with the structure morphism $\pi$ of projective space equals $f$, the requirement that for each $i$ and each open $V$ contained in $\varphi^{-1}$ of the basic open set of $X_i$ the map $\Gamma(X,V)\to\Gamma(L,V)$, $g\mapsto g\cdot(\sigma_i|_V)$, is bijective, and the requirement that on $\varphi^{-1}$ of the basic open set of $X_i$ the pulled-back section given by the ratio $X_j/X_i$ carries $\sigma_i|$ to $\sigma_j|$. Assume further that $\varphi$ is finite. Then there is $m_0\in\mathbb N$ such that for every $m\ge m_0$ and every ordered affine cover $\mathcal W$ of $X$ (a finite linearly ordered family of affine opens with supremum $\top$) the group $\ker(d^1)/\operatorname{im}(d^0)$ of the Čech complex of the $\mathcal O$-module presheaf of sections of $L^{\otimes m}$ over $\mathcal W$ is a subsingleton, i.e. $\check H^1(\mathcal W,L^{\otimes m})=0$; here $L^{\otimes m}$ is formed by the recursion $L^{\otimes 0}=\mathbf 1$, $L^{\otimes(n+1)}=L^{\otimes n}\otimes L$.
--
--   This is the degree-one case of Serre's vanishing theorem, in the form needed here: the presentation $\mathfrak P$ identifies $L$ with the pullback of $\mathcal O(1)$ along a finite morphism $\varphi$ to $\mathbb P^N_k$, and vanishing of $\check H^1$ is obtained for all sufficiently high tensor powers and, by independence of the cover, for every finite ordered affine cover. It is used in the construction of sections of powers of the theta bundle on the relative Picard scheme over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorPow_of_isFinite_toProj
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (N : ℕ) (𝔓 : L.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ 𝒲 : X.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules f (L.tensorPow m)).HSucc 𝒲 0) := by sorry
