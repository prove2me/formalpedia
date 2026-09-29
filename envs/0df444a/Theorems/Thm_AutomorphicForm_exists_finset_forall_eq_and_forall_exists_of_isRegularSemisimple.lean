-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
-- name    : AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/5580c4b6-f470-5cea-bdc3-5654f18b340a
-- title:
--   Finiteness of double cosets meeting an orbital integrand's support
-- statement:
--   Let $K$ be a number field and $v$ a maximal ideal of its ring of integers $\mathcal{O}_K$, with completion $K_v$; write $U \subseteq \mathrm{GL}_2(K_v)$ for the set of invertible matrices both of whose own entries and whose inverse's entries lie in the valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers K` (this is [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100)). Let $\gamma \in \mathrm{GL}_2(K_v)$ satisfy [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), that is, $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $K_v$, and let $T$ denote the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$. Let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a function for which there is a finite set $F_0$ of elements of $\mathrm{GL}_2(K_v)$ such that every $g$ with $f(g) \neq 0$ satisfies $c^{-1}g \in U$ for some $c \in F_0$; thus $f$ vanishes outside finitely many left cosets $cU$. The assertion is that there exists a finite set $S \subseteq \mathrm{GL}_2(K_v)$ such that, first, for $s, s' \in S$, $t \in T$ and $u \in U$, the equality $s' = tsu$ forces $s' = s$, and second, every $x \in \mathrm{GL}_2(K_v)$ with $f(x^{-1}\gamma x) \neq 0$ can be written $x = tsu$ with $s \in S$, $t \in T$ and $u \in U$.
--
--   This is the finiteness statement underlying the orbital integral of $f$ at a regular semisimple $\gamma$: the elements of $S$ represent, without repetition, exactly those double cosets $T s U$ that meet the support of $x \mapsto f(x^{-1}\gamma x)$. It is used to express such orbital integrals as finite sums over double cosets, and thence in the comparison of local Hecke operators at an inert prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem
AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ g : GL (Fin 2) (v.adicCompletion K), f g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ AutomorphicForm.localIntegralSet K v) :
    ∃ S : Finset (GL (Fin 2) (v.adicCompletion K)),
     (
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s
     ) ∧
     (
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u
     ) := by sorry
