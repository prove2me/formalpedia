-- Prove2me | Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
-- name    : AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6512a05d-b9f2-5dcc-aafb-678cc9c91fe3
-- title:
--   Type pieces are stable under equivariant surjections of finite-dimensional stable subspaces
-- statement:
--   Let $K$ and $G$ be groups, $\iota\colon K\to G$ an injective group homomorphism, $n$ a natural number, and for each $i\in\{0,\dots,n-1\}$ let $W_i$ be a complex vector space carrying a representation $\rho_i$ of $K$. For a representation $\sigma$ of $K$ on $W$, write $\mathcal F_\sigma = \mathtt{typeSubmodule}\,\iota\,\sigma$ for the $\mathbb C$-span inside $G\to\mathbb C$ of all values $T(v)$, $v\in W$, where $T\colon W\to(G\to\mathbb C)$ runs over the $\mathbb C$-linear maps satisfying $T(\sigma(k)v)(x)=T(v)(x\,\iota(k))$ for all $k\in K$, $v\in W$, $x\in G$. Let $S,S'$ be $\mathbb C$-subspaces of $G\to\mathbb C$ with $S$ finite-dimensional, both stable under the right translations $s\mapsto\bigl(x\mapsto s(x\,\iota(k))\bigr)$ for all $k\in K$, and let $\theta\colon S\to S'$ be a surjective $\mathbb C$-linear map that commutes with these right translations, i.e. $\theta\bigl(x\mapsto s(x\,\iota(k))\bigr)=\bigl(x\mapsto\theta(s)(x\,\iota(k))\bigr)$ for all $k\in K$ and $s\in S$. If $S\subseteq\sum_i\mathcal F_{\rho_i}$, then $S'\subseteq\sum_i\mathcal F_{\rho_i}$.
--
--   This is the invariance of the sum of the $\rho_i$-type pieces of $G\to\mathbb C$ under right-translation-equivariant surjective images of its finite-dimensional stable subspaces, the point being that a type piece is defined through intertwiners out of the $W_i$ themselves rather than out of their subquotients. It is used in the construction and analysis of the archimedean cut-off and convolution operators on spaces of automorphic forms, where the operators are equivariant surjections between finite-dimensional stable spaces of functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S S' : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS' : ∀ k : K, ∀ s ∈ S', (fun x => s (x * ι k)) ∈ S')
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S)
    (θ : S →ₗ[ℂ] S') (hθs : Function.Surjective θ)
    (hθ : ∀ (k : K) (s : S),
      (θ ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ : G → ℂ) = fun x => (θ s : G → ℂ) (x * ι k))
    (hSA : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    S' ≤ ⨆ i, typeSubmodule ι (ρ i) := by sorry
