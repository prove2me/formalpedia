-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/78e93a4f-99e1-5d6a-a620-a56dfabe8c11
-- title:
--   Finiteness of twisted double cosets meeting the support
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal{O}_K$, write $K_v$ for the $v$-adic completion, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$. Let $\sigma$ act on $L \otimes_K K_v$ by $\sigma \otimes \mathrm{id}$ and on $\mathrm{GL}_2$ entrywise, written `sigmaGL`. Assume the norm string $\prod_{i=0}^{n-1} \sigma^i(\delta)$, $n = \dim_K L$, is regular semisimple, that is $\operatorname{tr}^2 - 4\det$ of it is a unit of $L \otimes_K K_v$. Let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be a function for which there is a finite set $F_0$ such that every $g$ with $\varphi(g) \neq 0$ satisfies $c^{-1}g \in$ [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) for some $c \in F_0$, this last set consisting of those $g$ with $g$ and $g^{-1}$ both in `integralMatrixSet` of the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`. Then there is a finite set $S$ such that: for $s, s' \in S$, $t$ in the twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$ and $u$ in the semi-local integral set, $s' = tsu$ forces $s' = s$; and every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$ is of the form $tsu$ with $s \in S$, $t$ twisted-centralising and $u$ in the semi-local integral set.
--
--   This is the finiteness statement that makes a twisted orbital integral of $\varphi$ at $\delta$ a finite sum over twisted double cosets $T_\delta \, s \, U$, the twisted analogue of the corresponding assertion for ordinary conjugation by [`AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple`](thm.html#AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple). It is used in the comparison of twisted orbital integrals with their untwisted shadows and in the construction of matching local Hecke operators at an inert prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TensorProduct
open scoped TensorProduct.RightActions

theorem
AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφs : ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), φ g ≠ 0 →
        ∃ c ∈ F₀, c⁻¹ * g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    ∃ S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
     (
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∀ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, s' = t * s * u → s' = s
     ) ∧
     (
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
          ∃ s ∈ S,
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
              ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, x = t * s * u
     ) := by sorry
