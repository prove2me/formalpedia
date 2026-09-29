-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4797c58f-01e9-5b74-99f9-c47ade9cdbd6
-- title:
--   Snapper polynomiality for coherent 𝒪-module presheaf data
-- statement:
--   Let $k$ be a field and $\pi\colon V\to\operatorname{Spec}k$ a proper morphism of schemes, and let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$ together with affine opens $U_i\subseteq V$ whose supremum is $\top$. Let $G$ be an $\mathcal O$-module presheaf datum over $\pi$, that is, an assignment $U\mapsto G(U)$ of an abelian group to each open of $V$ carrying compatible $k$- and $\Gamma(V,U)$-module structures, together with $k$-linear restrictions $G(U')\to G(U)$ for $U\le U'$ that are semilinear over the restriction of sections and are functorial. Assume $G$ is coherent, i.e. $G(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; quasi-coherent, i.e. for every affine open $U$ and $f\in\Gamma(V,U)$ every element of $G(V_f)$ becomes, after multiplication by some power of $f$, a restriction from $G(U)$, and every element of $G(U)$ restricting to $0$ on $V_f$ is killed by a power of $f$; and supported in a closed subset $Y\subseteq V$, i.e. $G(U)$ is a subsingleton for every affine open $U$ disjoint from $Y$. Let $d\in\mathbb N$ with $\operatorname{topologicalKrullDim} Y\le d$. Let $L$ be a module object on $V$ which is locally trivial: every point has an open neighbourhood $U$ such that the pullback of $L$ along $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules on $U$. Write $L^{\otimes n}$ for the iterated tensor power ($L^{\otimes 0}$ the monoidal unit, $L^{\otimes(n+1)}=L^{\otimes n}\otimes L$), and let $G\otimes L^{\otimes n}$ be the open-by-open twist $U\mapsto G(U)\otimes_{\Gamma(V,U)}\Gamma(L^{\otimes n},U)$. Then there is a polynomial $p\in\mathbb Q[X]$ with $\deg p\le d$ such that for every natural number $n$ the Euler characteristic $\sum_{i<\#\iota}(-1)^i\dim_k\check H^i(K,G\otimes L^{\otimes n})$, computed as the alternating sum of the $k$-dimensions of the Čech cohomology of the cover $K$, equals $p(n)$ in $\mathbb Q$.
--
--   This is Snapper's polynomiality theorem, in a form adapted to presheaf data given open by open rather than to sheaves on $V$, so that it is stable under the dévissage of coherent sheaves by kernels, cokernels and push-forwards from closed subschemes. It is the source of the Snapper polynomial whose coefficients are compared with ranks at stalks and with degrees of endomorphisms, and it feeds the degree computations for the relative group law on Jacobians of curves with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq
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
