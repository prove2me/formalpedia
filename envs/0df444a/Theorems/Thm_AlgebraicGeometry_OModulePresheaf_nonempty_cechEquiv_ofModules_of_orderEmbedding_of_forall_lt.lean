-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/98e646d8-aee7-52e3-9ca4-c579414f62c8
-- title:
--   Adjoining a largest affine chart preserves Čech cohomology
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme and let $\pi\colon V\to\operatorname{Spec} R$ be a separated morphism, and let $M$ be a sheaf of $\mathcal O_V$-modules. Form the $\mathcal O$-module presheaf `OModulePresheaf.ofModules π M` on the opens of $V$, whose value on $U$ is $\Gamma(M,U)$ with its $\Gamma(V,U)$-action, its $R$-action obtained from $\pi$, and restriction maps those of $M$; assume it satisfies `IsQuasicoherent`, i.e. for every affine open $U\subseteq V$ and every $f\in\Gamma(V,U)$, each section $x$ over the basic open $V_f$ satisfies $f^n\cdot x=\mathrm{res}(y)$ for some $n$ and some section $y$ over $U$, and each section over $U$ restricting to $0$ on $V_f$ is annihilated by some power of $f$. Let $K$ and $K'$ be ordered affine covers of $V$, i.e. finite linearly ordered index types together with affine opens whose supremum is $\top$. Assume given an order embedding $e\colon K.\iota\hookrightarrow K'.\iota$ with $K'.U(e\,i)=K.U\,i$ for all $i$, and an index $j_0$ of $K'$ such that every index of $K'$ is either $j_0$ or of the form $e\,i$, and $e\,i<j_0$ for all $i$. Then the degree-zero cohomology modules, namely the kernels of the Čech differentials in degree $0$, are isomorphic as $R$-modules for $K'$ and for $K$, and likewise for every $i\in\mathbb N$ the degree-$(i+1)$ cohomology modules $\ker(d_{i+1})/\mathrm{im}(d_i)$ for $K'$ and for $K$ are isomorphic as $R$-modules. The conclusion asserts non-emptiness of the sets of such isomorphisms; no particular comparison map is specified.
--
--   This is the inductive step in the comparison of alternating Čech cohomology for two finite ordered affine covers of a separated scheme, one obtained from the other by adjoining a single affine chart placed above all the others. It feeds into [`AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated`](thm.html#AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated), which states the independence of the Čech cohomology of a quasi-coherent module of the chosen ordered affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (M : V.Modules) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (K K' : V.OrderedAffineCover) (e : K.ι ↪o K'.ι) (hU : ∀ i, K'.U (e i) = K.U i)
    (j₀ : K'.ι) (hj₀ : ∀ j : K'.ι, j = j₀ ∨ j ∈ Set.range e) (hlt : ∀ i, e i < j₀) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K' ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K' i ≃ₗ[R]
        (OModulePresheaf.ofModules π M).HSucc K i) := by sorry
