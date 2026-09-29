-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2
-- name    : AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/dbbf0b48-797c-5347-a72e-07ce03bd679d
-- title:
--   Snapper polynomiality for coherent presheaf data twisted by a line bundle
-- statement:
--   Let $k$ be a field, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} k$ a proper morphism, and let $K$ be an ordered affine cover of $V$: a finite, linearly ordered index type $\iota$ together with opens $U_i\subseteq V$, each affine, with $\bigsqcup_i U_i=\top$. Let $G$ be an `OModulePresheaf` for $\pi$, that is, an assignment of a $k$-module and $\Gamma(V,U)$-module $G(U)$ to each open $U$ (the two actions being compatible via the algebra structure coming from $\pi$) together with $k$-linear restriction maps semilinear over $\mathcal O_V$ and functorial. Assume $G$ is coherent, i.e. $G(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; quasi-coherent, i.e. for every affine open $U$ and $f\in\Gamma(V,U)$ every section over the basic open $D(f)$ becomes a restriction from $U$ after multiplication by some $f^n$, and every section on $U$ restricting to $0$ on $D(f)$ is annihilated by some $f^n$; and supported in a closed set $Y\subseteq V$, i.e. $G(U)$ is a subsingleton whenever the affine open $U$ is disjoint from $Y$. Let $d\in\mathbb N$ with $\operatorname{topologicalKrullDim} Y\le d$. Let $L$ be an object of `V.Modules` which is locally trivial: every point of $V$ has an open neighbourhood $U$ over which the pullback of $L$ along $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules. Then there is $p\in\mathbb Q[X]$ with $\deg p\le d$ such that for every $n\in\mathbb N$ the Euler characteristic $\sum_{i<\#\iota}(-1)^i\dim_k \check H^i(K,\,\cdot\,)$ of the open-by-open twist $U\mapsto G(U)\otimes_{\Gamma(V,U)}\Gamma(L^{\otimes n},U)$, where $L^{\otimes n}$ is the $n$-fold monoidal power of $L$ (with $L^{\otimes 0}$ the monoidal unit), equals $p(n)$.
--
--   This is Snapper's polynomiality theorem for the Euler characteristic of a coherent sheaf twisted by the powers of an invertible sheaf, stated for presheaf data given open by open so that it is stable under the dévissage of coherent sheaves on a proper $k$-scheme and computed through alternating Čech cohomology on a fixed finite affine cover. It is used to obtain the corresponding polynomiality statement for twists by a further coherent datum, en route to the numerical invariants of proper $k$-schemes needed later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (G : OModulePresheaf π)
    (hc : G.IsCoherent) (hq : G.IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : G.SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((G.twist (L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) := by sorry
