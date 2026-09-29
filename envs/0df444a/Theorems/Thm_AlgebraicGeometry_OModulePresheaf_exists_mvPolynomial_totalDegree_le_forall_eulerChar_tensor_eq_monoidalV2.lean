-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
-- name    : AlgebraicGeometry.OModulePresheaf.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/b2ca76cc-db12-52fa-b775-dc34621b1c7e
-- title:
--   Snapper–Kleiman polynomiality of Čech Euler characteristics
-- statement:
--   Let $k$ be a field, let $\pi\colon V\to\operatorname{Spec}k$ be a proper morphism of schemes, and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index set $K.\iota$ together with affine opens $U_i\subseteq V$ whose supremum is $\top$. Let $M$ be a sheaf of $\mathcal O_V$-modules, and consider the presheaf of $k$-modules $U\mapsto\Gamma(M,U)$ attached to it by $\pi$. Assume: it is coherent, i.e. $\Gamma(M,U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; it is quasi-coherent, i.e. for every affine open $U$ and $f\in\Gamma(V,U)$, every section over the basic open $V_f$ becomes, after multiplication by some power of $f$, a restriction of a section over $U$, and every section over $U$ dying on $V_f$ is killed by a power of $f$; and it is supported in a closed subset $Y\subseteq V$, i.e. $\Gamma(M,U)=0$ for every affine open $U$ disjoint from $Y$. Let $d\in\mathbb N$ with $\operatorname{topologicalKrullDim}Y\le d$. Let $(L_i)_{i\in\iota}$ be a finite family of $\mathcal O_V$-modules, each invertible in the sense that every point of $V$ has an open neighbourhood $U$ on which the pullback of $L_i$ along $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules of $U$. Then there is $P\in\mathbb Q[X_i: i\in\iota]$ of total degree at most $d$ such that for all $a,b\colon\iota\to\mathbb N$ and every $\mathcal O_V$-module $N$ whose class in the skeleton of the monoidal category $V.\mathrm{Modules}$ satisfies $[N]\cdot\prod_i[L_i]^{b_i}=\prod_i[L_i]^{a_i}$ (i.e. $N\otimes\bigotimes_iL_i^{\otimes b_i}\cong\bigotimes_iL_i^{\otimes a_i}$), the Čech Euler characteristic $\sum_{j<\#\iota_K}(-1)^j\dim_k\check H^j(K,M\otimes N)$, viewed in $\mathbb Q$, equals $P\bigl((a_i-b_i)_i\bigr)$.
--
--   This is Snapper's polynomiality theorem, with Kleiman's bound of the total degree by the dimension of the support: the Euler characteristic of $M\otimes L_1^{\otimes n_1}\otimes\cdots\otimes L_r^{\otimes n_r}$ is a numerical polynomial in $(n_1,\dots,n_r)\in\mathbb Z^r$, the formulation with pairs $(a,b)$ of natural numbers and an auxiliary module $N$ encoding negative exponents. It underlies the intersection numbers used in the treatment of Euler characteristics on Jacobians, and is cited for the behaviour of $\chi$ under duality and under tensoring by powers of invertible modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
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
