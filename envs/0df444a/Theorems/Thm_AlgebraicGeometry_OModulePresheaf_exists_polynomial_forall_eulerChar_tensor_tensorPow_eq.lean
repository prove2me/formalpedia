-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/65b7b7d8-d438-5e0b-b3ae-6d8966d39c20
-- title:
--   Snapper polynomiality of χ(M⊗ L^{⊗ n})
-- statement:
--   Let $k$ be a field and $\pi\colon V\to\operatorname{Spec} k$ a proper morphism of schemes. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index set $\iota$ together with opens $U_i\subseteq V$, each an affine open, with $\bigsqcup_i U_i=\top$. Let $M$ be a sheaf of $\mathcal O_V$-modules, and consider the presheaf of $k$-modules $U\mapsto\Gamma(M,U)$ with its $\Gamma(V,U)$-module structures and restriction maps, the $k$-structure coming from $\pi$. Assume: for every affine open $U$ the module $\Gamma(M,U)$ is finite over $\Gamma(V,U)$; for every affine open $U$ and $f\in\Gamma(V,U)$, each section over the basic open $V_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $V_f$ is annihilated by some power of $f$; there is a closed $Y\subseteq V$ with $\Gamma(M,U)$ trivial for every affine open $U$ disjoint from $Y$, and a natural number $d$ with $\operatorname{topologicalKrullDim} Y\le d$. Let $L$ be a sheaf of $\mathcal O_V$-modules such that every point of $V$ has an open neighbourhood $U$ on which the pullback of $L$ along $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules on $U$. Then there is a polynomial $p\in\mathbb Q[X]$ with $\deg p\le d$ such that for every $n\in\mathbb N$ the Euler characteristic $\sum_{i<|\iota|}(-1)^i\dim_k \check H^i(K,\,\cdot\,)$ of the presheaf attached to $M\otimes L^{\otimes n}$, where $L^{\otimes n}$ is built from the unit by iterated tensoring with $L$, equals $p(n)$.
--
--   This is Snapper's polynomiality theorem in the form with a single invertible sheaf, with Kleiman's bound on the degree by the dimension of the support of $M$; the Euler characteristic is the alternating Čech one for the fixed finite affine cover $K$, so that no comparison with derived-functor cohomology enters the formulation. It feeds the several-line-bundle version with a multivariate polynomial, the version for modules finite by sections, and the vanishing of coefficients used in the study of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((OModulePresheaf.ofModules π (M ⊗ L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) := by sorry
