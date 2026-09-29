-- Prove2me | Theorems.Thm_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one
-- name    : AutomorphicForm.twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/1edca68a-5346-5931-9417-45b766937c87
-- title:
--   Twisted centralizer of a norm of regular semisimple γ
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a commutative $K$-algebra. Assume $\operatorname{finrank}_K L = 2$, and let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$. Write $\sigma$ also for the induced automorphism of $\mathrm{GL}_2(L \otimes_K A)$ obtained by applying $\sigma \otimes \mathrm{id}_A$ entrywise ([`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202)), and let [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) denote the group homomorphism $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced entrywise by $a \mapsto 1 \otimes a$. Let $\gamma \in \mathrm{GL}_2(A)$ be regular semisimple in the sense that $(\operatorname{tr}\gamma)^2 - 4\det\gamma$ is a unit of $A$, and let $\delta \in \mathrm{GL}_2(L \otimes_K A)$ satisfy the hypothesis that $1$ is a norm conjugator for $(\gamma,\delta)$, i.e. $\mathrm{toTensorGL}(\gamma) = 1^{-1} \cdot \bigl(\prod_{i < \operatorname{finrank}_K L} \sigma^{i}(\delta)\bigr) \cdot 1$; by the degree hypothesis this says $\mathrm{toTensorGL}(\gamma) = \delta \cdot \sigma(\delta)$. The conclusion is an equality of subgroups of $\mathrm{GL}_2(L \otimes_K A)$: the $\sigma$-twisted centralizer $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta$ equals the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) of the centralizer of $\{\gamma\}$ in $\mathrm{GL}_2(A)$.
--
--   This is the standard identification, in the setting of base change for $\mathrm{GL}(2)$ along a quadratic extension, of the twisted centralizer of a $\sigma$-conjugacy class representative whose norm is a regular semisimple element $\gamma$ with the centralizer of $\gamma$ itself; it is what makes twisted orbital integrals at $\delta$ comparable with ordinary orbital integrals at $\gamma$. It is used in the construction of twisted orbital integrals with prescribed archimedean test factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormConjugator K L A σ γ δ 1) :
    AutomorphicForm.twistedCentralizer K L A σ δ =
      (Subgroup.centralizer {γ}).map (AutomorphicForm.toTensorGL K L A) := by sorry
