-- Prove2me | Theorems.Thm_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
-- name    : AutomorphicForm.exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/05c6e083-b36e-5d8c-89f8-924820568d61
-- title:
--   Prescribing archimedean and semi-local components of adelic GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $S$ be a finite set of nonzero primes of the ring of integers $\mathcal{O}_K$, let $a \in \mathrm{GL}_2(L_\infty)$ be an invertible $2\times 2$ matrix over the infinite adele ring of $L$, and let $x$ assign to every nonzero prime $v$ of $\mathcal{O}_K$ an element $x_v \in \mathrm{GL}_2(L \otimes_K K_v)$, where $K_v$ is the $v$-adic completion. Then there is an element $g \in \mathrm{GL}_2(\mathbb{A}_L)$, over the full adele ring of $L$, such that: the entrywise image of $g$ under the projection $\mathbb{A}_L \to L_\infty$ equals $a$; for every $v \in S$ the semi-local component of the finite part of $g$ at $v$ equals $x_v$; and for every $v \notin S$ that semi-local component lies in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136). Here the semi-local component at $v$ is obtained by applying entrywise the ring homomorphism that evaluates a finite adele of $L$ at all the places $w$ of $L$ above $v$ and then transports the resulting tuple through the inverse of the base-change isomorphism identifying $\prod_{w \mid v} L_w$ with $L \otimes_K K_v$; and `semiLocalIntegralSet K L v` consists of those $h \in \mathrm{GL}_2(L \otimes_K K_v)$ for which both the matrix of $h$ and the matrix of $h^{-1}$ lie in `integralMatrixSet` of the set of semi-local integers, that is of the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`.
--
--   This is the restricted-product surjectivity statement that allows adelic points of $\mathrm{GL}_2$ over $L$ to be spliced together from a prescribed archimedean matrix, prescribed semi-local data at the finitely many primes of $K$ in $S$, and semi-locally integral data elsewhere; the family $(x_v)$ outside $S$ is simply ignored. It is used when factorisable test functions on $\mathrm{GL}_2(\mathbb{A}_L)$ are evaluated at spliced points, and it feeds the comparison of hyperbolic terms in the winding computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped TensorProduct in

theorem AutomorphicForm.exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : GL (Fin 2) (InfiniteAdeleRing L))
    (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ g : GL (Fin 2) (AdeleRing (𝓞 L) L),
      AdelicLevel.glArch (𝓞 L) L g = a ∧
      (∀ v ∈ S, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) = x v) ∧
      ∀ v ∉ S, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) ∈
        AutomorphicForm.semiLocalIntegralSet K L v := by sorry
