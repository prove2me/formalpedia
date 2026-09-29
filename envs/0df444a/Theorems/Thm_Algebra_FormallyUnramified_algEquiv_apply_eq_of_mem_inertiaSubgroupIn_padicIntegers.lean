-- Prove2me | Theorems.Thm_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
-- name    : Algebra.FormallyUnramified.algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/bfa36450-40aa-55b5-8f49-94de9b204127
-- title:
--   Inertia fixes ℚ̄ₚ-points of finite unramified ℤₚ-algebras
-- statement:
--   Fix a prime $p$ and let $B$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure such that $B$ is finite as a $\mathbb{Z}_p$-module and formally unramified over $\mathbb{Z}_p$. Write $\overline{\mathbb{Q}}_p$ for `PadicAlgCl p` and let $\mathcal{O} =$ [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) be the valuation subring attached to its valuation with values in $\mathbb{R}_{\ge 0}$. Let $\sigma$ be a $\mathbb{Q}_p$-algebra automorphism of $\overline{\mathbb{Q}}_p$ belonging to `(padicIntegers p).inertiaSubgroupIn ℚ_[p]`, that is, to the image under the inclusion of the decomposition subgroup of $\mathcal{O}$ over $\mathbb{Q}_p$ into the full automorphism group of the inertia subgroup of $\mathcal{O}$ over $\mathbb{Q}_p$: so $\sigma$ arises from an automorphism preserving $\mathcal{O}$ and acting trivially on the residue field of $\mathcal{O}$. Then for every $\mathbb{Z}_p$-algebra homomorphism $h \colon B \to \overline{\mathbb{Q}}_p$ and every $y \in B$ one has $\sigma(h(y)) = h(y)$.
--
--   This is the statement that the finite Galois set $\operatorname{Hom}_{\mathbb{Z}_p}(B,\overline{\mathbb{Q}}_p)$ attached to a finite unramified $\mathbb{Z}_p$-algebra is unramified, i.e. all such points are defined over the maximal unramified extension of $\mathbb{Q}_p$. It is used in the construction of the connected–étale sequence over $\mathbb{Z}_p$, via [`HopfAlgebra.exists_connected_etale_sequence_padicInt`](thm.html#HopfAlgebra.exists_connected_etale_sequence_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v

open scoped PadicInt

theorem Algebra.FormallyUnramified.algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
    (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B]
    [Algebra.FormallyUnramified ℤ_[p] B]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p])
    (h : B →ₐ[ℤ_[p]] PadicAlgCl p) (y : B) : σ (h y) = h y := by sorry
