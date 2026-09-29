-- Prove2me | Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing
-- name    : AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/3d023c72-f79b-50c2-8e15-a34281b55f50
-- title:
--   Non-degenerate invariant pairing forces dual K-types
-- statement:
--   Let $\iota\colon K\to G$ be an injective homomorphism of groups, let $n\in\mathbb N$, and for each $i\in\mathrm{Fin}\,n$ let $W_i$ be a complex vector space carrying a representation $\rho_i$ of $K$. For a representation $\sigma$ of $K$ on $W$, the submodule `typeSubmodule` $\iota$ $\sigma$ of the space $G\to\mathbb C$ of all complex-valued functions on $G$ is the $\mathbb C$-span of all functions lying in the range of some $\mathbb C$-linear $T\colon W\to(G\to\mathbb C)$ satisfying $T(\sigma(k)v)(x)=T(v)(x\,\iota(k))$ for all $k\in K$, $v\in W$, $x\in G$. Let $S$ and $T$ be $\mathbb C$-submodules of $G\to\mathbb C$ with $S$ finite-dimensional, each stable under the right translations $f\mapsto f(\,\cdot\,\iota(k))$ for all $k\in K$, and let $\beta\colon S\to T\to\mathbb C$ be a $\mathbb C$-bilinear map which is invariant in the sense that $\beta$ applied to the simultaneous translates of $s\in S$ and $t\in T$ by $\iota(k)$ equals $\beta(s,t)$, and which is non-degenerate on the right: if $\beta(s,t)=0$ for all $s\in S$ then $t=0$. Assume $S\le\bigsqcup_i$ `typeSubmodule` $\iota$ $\rho_i$ (supremum of submodules). The conclusion is that $T\le\bigsqcup_i$ `typeSubmodule` $\iota$ $(\rho_i)^{\vee}$, the corresponding supremum formed from the contragredient representations.
--
--   This is the duality step in the analysis of $K$-types of spaces of functions on $G$: a finite-dimensional side whose types are among $\rho_1,\dots,\rho_n$ pairs invariantly and non-degenerately only with functions whose types are among the contragredients $\rho_i^{\vee}$. It is used in the construction of elements of the span of right translates lying in the archimedean dual cut submodule with prescribed right convolution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S T : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S) (hT : ∀ k : K, ∀ t ∈ T, (fun x => t (x * ι k)) ∈ T)
    (β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ)
    (hβ : ∀ (k : K) (s : S) (t : T), β ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ ⟨fun x => (t : G → ℂ) (x * ι k), hT k t t.2⟩ = β s t)
    (hnd : ∀ t : T, (∀ s : S, β s t = 0) → t = 0)
    (hSle : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    T ≤ ⨆ i, typeSubmodule ι (ρ i).dual := by sorry
