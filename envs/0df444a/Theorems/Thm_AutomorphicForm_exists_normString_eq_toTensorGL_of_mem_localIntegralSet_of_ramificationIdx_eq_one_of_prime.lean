-- Prove2me | Theorems.Thm_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
-- name    : AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/751b2750-1138-5891-8cb8-e817c1ef5055
-- title:
--   Integral norm-string witnesses at unramified places of prime degree
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra whose degree $n = \operatorname{finrank}_K L$ is prime, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a height-one prime of $\mathcal{O}_K$ such that every height-one prime $w$ of $\mathcal{O}_L$ lying under $v$ (i.e. with $\mathrm{under}\,(\mathcal{O}_K)\,w = v$) has ramification index $e(w \mid v) = 1$. Let $\gamma \in \mathrm{GL}_2(K_v)$, where $K_v$ is the $v$-adic completion of $K$, lie in the local integral set, that is, all entries of $\gamma$ and of $\gamma^{-1}$ lie in the valuation ring $\mathcal{O}_v$ of $K_v$, and assume the discriminant $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ has valuation $1$ (so is a unit of $\mathcal{O}_v$). Then there exists $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ all of whose entries, and all of whose inverse's entries, lie in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$ in $L \otimes_K K_v$ under `HeightOneSpectrum.tensorAdicCompletionIntegersTo`, such that the norm string $\prod_{i=0}^{n-1} (\sigma^{i} \otimes \mathrm{id})(\delta)$, taken in the order $i = 0, \dots, n-1$ with $\sigma$ acting entrywise through the left tensor factor, equals the image of $\gamma$ under the map $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ induced by $a \mapsto 1 \otimes a$.
--
--   This is the integral local surjectivity statement for twisted ($\sigma$-)norms on $\mathrm{GL}_2$ at a place unramified in a degree-$\ell$ extension, in the regular semisimple case signalled by a unit discriminant; the conjugator is trivial, the witness being an exact norm string rather than a norm string conjugate to $\gamma$. It feeds the passage from local to adelic norms in cyclic base change for $\mathrm{GL}_2$, being used by [`AutomorphicForm.exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime`](thm.html#AutomorphicForm.exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime) and by [`AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two`](thm.html#AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : γ ∈ AutomorphicForm.localIntegralSet K v)
    (hdisc : Valued.v (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    ∃ δ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
      AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) γ := by sorry
