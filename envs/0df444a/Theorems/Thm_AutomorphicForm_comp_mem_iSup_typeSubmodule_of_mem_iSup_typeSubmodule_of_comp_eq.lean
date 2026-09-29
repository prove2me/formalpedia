-- Prove2me | Theorems.Thm_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq
-- name    : AutomorphicForm.comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/cf4a3547-2d0a-5332-95f3-bb914f74dcff
-- title:
--   Pullback of type submodules along a compatible homomorphism
-- statement:
--   Let $H$, $P$, $G$ be groups and let $\iota\colon H\to G$, $j\colon H\to P$, $\theta\colon P\to G$ be group homomorphisms with $\theta\circ j=\iota$. Let $I$ be an index type and, for each $i\in I$, let $W_i$ be a complex vector space carrying a representation $\rho_i$ of $H$. For a homomorphism $\kappa\colon H\to Q$, write $\mathcal T_\kappa(\rho_i)$ for the submodule [`AutomorphicForm.typeSubmodule`](def/AutomorphicForm_IsotypicCuspSpace.html#L471) of $Q\to\mathbb C$, namely the $\mathbb C$-span of all functions lying in the range of some $\mathbb C$-linear map $T\colon W_i\to (Q\to\mathbb C)$ that is right equivariant in the sense that $T(\rho_i(k)v)(x)=T(v)(x\,\kappa(k))$ for all $k\in H$, $v\in W_i$ and $x\in Q$. The assertion is: if $f\colon G\to\mathbb C$ belongs to the supremum $\bigsqcup_i \mathcal T_\iota(\rho_i)$ of the type submodules taken with respect to $\iota$, then the pullback $p\mapsto f(\theta(p))$, a function $P\to\mathbb C$, belongs to the corresponding supremum $\bigsqcup_i \mathcal T_j(\rho_i)$ of the type submodules taken with respect to $j$.
--
--   This is the transport statement for $\rho$-isotypic pieces of spaces of complex-valued functions on a group under pullback along a homomorphism compatible with the two given inclusions of $H$. It is used in the construction of finite-dimensional bi-invariant pieces of spaces of automorphic forms, being cited by [`AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne`](thm.html#AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq
    {H P G : Type*} [Group H] [Group P] [Group G]
    (ι : H →* G) (j : H →* P) (θ : P →* G) (hθ : θ.comp j = ι)
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (f : G → ℂ) (hf : f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)) :
    (fun p : P => f (θ p)) ∈ ⨆ i, AutomorphicForm.typeSubmodule j (ρ i) := by sorry
