-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
-- name    : AutomorphicForm.exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6f30795d-9bfc-50d0-9ac4-07219164d8d4
-- title:
--   Prime-degree twisted conjugacy: exact norm in the centraliser
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and suppose the degree $\operatorname{finrank}_K L$ is a prime number; let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$. Let $A$ be a commutative $K$-algebra, $\gamma \in \mathrm{GL}_2(A)$ and $\delta \in \mathrm{GL}_2(L \otimes_K A)$. Write $1 \otimes \gamma$ for the image `toTensorGL` of $\gamma$ under the map of general linear groups induced by $A \to L \otimes_K A$, $a \mapsto 1 \otimes a$; write $\sigma$ also for the entrywise action `sigmaGL` on $\mathrm{GL}_2(L \otimes_K A)$ coming from $\sigma \otimes \mathrm{id}_A$; and for $\mu \in \mathrm{GL}_2(L \otimes_K A)$ let `normString` be $N\mu = \prod_{i<[L:K]} \sigma^{i}(\mu) = \mu\,\sigma(\mu)\cdots\sigma^{[L:K]-1}(\mu)$ in that order. Assume `IsNormOf`: there exists $y \in \mathrm{GL}_2(L \otimes_K A)$ with $1 \otimes \gamma = y^{-1} (N\delta) y$. Then there exist $t, x \in \mathrm{GL}_2(L \otimes_K A)$ such that $t$ lies in the centraliser of the singleton $\{1 \otimes \gamma\}$, such that $N t = 1 \otimes \gamma$ on the nose, and such that $t = x^{-1} \delta\, \sigma(x)$.
--
--   This is the standard normalisation step in the theory of twisted (norm) conjugacy for $\mathrm{GL}_2$ in a cyclic base-change situation: an element whose norm string is conjugate to a rational $\gamma$ may be replaced, within its $\sigma$-twisted conjugacy class, by one whose norm string equals $1 \otimes \gamma$ exactly and which centralises it. It is used in the comparison of local weighted orbital integrals and in the vanishing statement for norms of central scalar multiples of global points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    ∃ t x : GL (Fin 2) (L ⊗[K] A),
      t ∈ Subgroup.centralizer
          ({AutomorphicForm.toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
      AutomorphicForm.normString K L A σ t = AutomorphicForm.toTensorGL K L A γ ∧
      t = x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x := by sorry
