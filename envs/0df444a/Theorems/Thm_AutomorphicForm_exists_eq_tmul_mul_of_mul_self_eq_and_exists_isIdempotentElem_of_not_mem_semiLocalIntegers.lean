-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
-- name    : AutomorphicForm.exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/13c56c03-e466-5cd6-938c-ed49de99a3ba
-- title:
--   Unramified uniformiser stays a uniformiser of the semi-local algebra
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$. Assume that every nonzero prime $w$ of $\mathcal{O}_L$ lying under which $v$ is found — that is, every $w$ whose contraction to $\mathcal{O}_K$ is $v$ — has ramification index $\mathrm{ramificationIdx}'$ equal to $1$ over $v$. Let $\varpi \in K$ have $v$-adic valuation exactly $\mathrm{exp}(-1)$, i.e. $\varpi$ is a uniformiser at $v$. Write $\mathcal{O}$ for [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98), the image of the canonical algebra map $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v \to L \otimes_K K_v$, where $K_v$ is the $v$-adic completion of $K$ and $\mathcal{O}_v$ its valuation ring, and regard $\varpi$ in $L \otimes_K K_v$ as $1 \otimes \varpi$. The conclusion is the conjunction of two assertions: first, for all $x, y \in \mathcal{O}$ with $x \cdot x = (1 \otimes \varpi)\, y$, there exists $z \in \mathcal{O}$ with $x = (1 \otimes \varpi)\, z$; second, for every $x \in L \otimes_K K_v$ not lying in $\mathcal{O}$, there exist $y \in \mathcal{O}$ and a nonzero idempotent $e \in \mathcal{O}$ with $(1 \otimes \varpi)\, x\, y = e$.
--
--   Under the identification $L \otimes_K K_v \cong \prod_{w \mid v} L_w$, with $\mathcal{O}$ corresponding to $\prod_{w \mid v} \mathcal{O}_w$, both clauses express that an unramified uniformiser $\varpi$ of $K_v$ remains a uniformiser at each $w \mid v$: the first says that the ideal $\varpi\mathcal{O}$ is radical (the local form of the fact that $\mathcal{O}_L/\mathfrak{p}\mathcal{O}_L$ is reduced at unramified $\mathfrak{p}$), the second that an element outside $\mathcal{O}$ has a pole of order at least one at some $w$, so that $\varpi x$ can be adjusted to an idempotent. It feeds the analysis of twisted centralizers and semi-local integral sets at a place with ramification index one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ϖ : K) (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) :
    (∀ x ∈ AutomorphicForm.semiLocalIntegers K L v, ∀ y ∈ AutomorphicForm.semiLocalIntegers K L v,
        x * x = ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * y →
        ∃ z ∈ AutomorphicForm.semiLocalIntegers K L v,
          x = ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * z) ∧
    (∀ x : L ⊗[K] v.adicCompletion K, x ∉ AutomorphicForm.semiLocalIntegers K L v →
        ∃ y ∈ AutomorphicForm.semiLocalIntegers K L v, ∃ e ∈ AutomorphicForm.semiLocalIntegers K L v,
          e ≠ 0 ∧ IsIdempotentElem e ∧
            ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * x * y = e) := by sorry
