-- Prove2me | Theorems.Thm_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem
-- name    : Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/758f6b3d-3cd6-5d5d-b9b4-1426044a8105
-- title:
--   Finite unramified algebras are split by a finite Galois subextension
-- statement:
--   Let $K$ be a field and let $E$ be a commutative $K$-algebra which is finite as a $K$-module and formally unramified over $K$ (so that $E$ is a finite étale $K$-algebra), both taken in a fixed universe. Let $\Omega$ be a field extension of $K$ which is normal over $K$ (in Mathlib's sense: algebraic over $K$ with every element splitting its minimal polynomial over $K$ in $\Omega$). The assertion is that there exists an intermediate field $L$ with $K \subseteq L \subseteq \Omega$ such that $L$ is finite-dimensional over $K$, the extension $L/K$ is Galois, and for every $K$-algebra homomorphism $\varphi \colon E \to \Omega$ and every $e \in E$ one has $\varphi(e) \in L$; that is, the single finite Galois subextension $L$ of $\Omega$ contains the image of every $K$-algebra map from $E$ into $\Omega$.
--
--   This is the elementary half of the description of finite étale algebras over a field in terms of finite sets with continuous Galois action: a finite étale algebra is split by one finite Galois extension, so that all its $\Omega$-valued points are already $L$-rational. It is used in the construction of the relative group law on Jacobians of curves with good reduction, where torsion points must be shown to be defined over a single finite Galois extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L := by sorry
