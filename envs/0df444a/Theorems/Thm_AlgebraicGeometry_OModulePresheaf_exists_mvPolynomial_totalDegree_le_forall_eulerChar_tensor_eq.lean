-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/baa6422f-71bc-509f-8195-e7d17e3f3e11
-- title:
--   Snapper–Kleiman polynomiality of Čech Euler characteristics
-- statement:
--   Let $k$ be a field, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} k$ a proper morphism, and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index set together with affine opens $U_i$ whose supremum is $\top$. Let $M$ be a sheaf of $\mathcal O_V$-modules such that the presheaf of sections $U\mapsto\Gamma(M,U)$, regarded as a presheaf of $k$-modules via $\pi$, is coherent ($\Gamma(M,U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$) and quasi-coherent (for every affine open $U$ and $f\in\Gamma(V,U)$, every section over $V$'s basic open $D(f)$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and every section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$). Let $Y\subseteq V$ be closed with $M$ supported in $Y$, in the sense that $\Gamma(M,U)$ is trivial for every affine open $U$ disjoint from $Y$, and let $d\in\mathbb N$ satisfy $\operatorname{topologicalKrullDim} Y\le d$. Let $(L_i)_{i\in\iota}$ be a finite family of invertible $\mathcal O_V$-modules, each locally isomorphic, after pullback along the inclusion of a suitable open neighbourhood of any given point, to the unit sheaf of modules. Then there is $P\in\mathbb Q[X_i\,:\,i\in\iota]$ of total degree at most $d$ such that for all $a,b\colon\iota\to\mathbb N$ and every $\mathcal O_V$-module $N$ whose isomorphism class satisfies $[N]\cdot\prod_i [L_i]^{b_i}=\prod_i [L_i]^{a_i}$ in the skeleton of $V$-modules under tensor product, the Euler characteristic $\sum_{j<\#\iota_K}(-1)^j\dim_k \check H^j(K,M\otimes N)$, computed from the alternating Čech complex attached to $K$, equals $P$ evaluated at $(a_i-b_i)_{i\in\iota}$ in $\mathbb Q$.
--
--   This is Snapper's polynomiality theorem for a finite family of line bundles, with Kleiman's bound of the total degree by the dimension of the support, formulated for the Čech Euler characteristic of an ordered affine cover and with the integral exponents encoded by a relation between isomorphism classes. It is the statement that makes intersection numbers well defined, and it is used here to obtain polynomiality of the degree along a line of endomorphisms of an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    {ι : Type*} [Fintype ι] (L : ι → V.Modules) (hL : ∀ i, Scheme.Modules.IsInvertible (L i)) :
    ∃ P : MvPolynomial ι ℚ, P.totalDegree ≤ d ∧
      ∀ (a b : ι → ℕ) (N : V.Modules),
        toSkeleton N * ∏ i, toSkeleton (L i) ^ b i = ∏ i, toSkeleton (L i) ^ a i →
          ((OModulePresheaf.ofModules π (M ⊗ N)).eulerChar K : ℚ) =
            MvPolynomial.eval (fun i => (a i : ℚ) - (b i : ℚ)) P := by sorry
