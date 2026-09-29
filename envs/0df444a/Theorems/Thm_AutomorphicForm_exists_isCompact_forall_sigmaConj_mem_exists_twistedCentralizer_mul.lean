-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
-- name    : AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/4e194e32-27b0-5d3e-bb8c-5ac1e5f92187
-- title:
--   Properness of twisted conjugation modulo the twisted centraliser
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal O_K$ with completion $K_v$, and let $\sigma$ be a $K$-algebra automorphism of $L$. Write $\sigma$ also for the ring automorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K K_v$ and for the induced group endomorphism of $\mathrm{GL}_2(L \otimes_K K_v)$ obtained by applying it entrywise. Let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ and set $N\delta = \prod_{i=0}^{n-1} \sigma^{i}(\delta) = \delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$, the product taken in this order with $n = \operatorname{finrank}_K L$ factors. Assume $N\delta$ is regular semisimple in the sense that $(\operatorname{tr} N\delta)^2 - 4\det N\delta$ is a unit of $L \otimes_K K_v$. Let $S$ be a compact subset of $\mathrm{GL}_2(L \otimes_K K_v)$. The conclusion asserts the existence of a compact subset $\Omega$ of $\mathrm{GL}_2(L \otimes_K K_v)$ such that every $x$ with $x^{-1}\,\delta\,\sigma(x) \in S$ factors as $x = t\,d$ with $d \in \Omega$ and $t$ in the $\sigma$-twisted centraliser of $\delta$, i.e. the subgroup of those $t$ with $t\,\delta\,\sigma(t)^{-1} = \delta$.
--
--   This is the properness, modulo the twisted centraliser, of the twisted conjugation map $x \mapsto x^{-1}\delta\,\sigma(x)$ at a finite place, the compactness input that makes twisted orbital integrals of compactly supported test functions converge. It is used in the construction of twisted orbital integrals for regular semisimple norms and in the matching statements comparing local test functions on $\mathrm{GL}_2$ over $K$ and over $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (S : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hS : IsCompact S) :
    ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ S →
          ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ d ∈ Ω, x = t * d := by sorry
