-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
-- name    : AutomorphicForm.isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e06e628e-4469-5060-b56f-9f8b11996737
-- title:
--   Finite double-coset sum realises a local orbital integral
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$, and $\gamma \in \mathrm{GL}_2(K_v)$ an element that is regular semisimple in the sense that $\mathrm{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $K_v$. Let $T =$ `Subgroup.centralizer {γ}` carry its Borel $\sigma$-algebra and let $\tau$ be a Haar measure on $T$. Write $U =$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for the set of $g \in \mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have all entries in the valuation ring $\mathcal{O}_v$. Let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ satisfy $f(u_1 g u_2) = f(g)$ for all $g$ and all $u_1, u_2 \in U$, and let $S$ be a finite subset of $\mathrm{GL}_2(K_v)$ such that (i) for $s, s' \in S$, $t \in T$ and $u \in U$, $s' = t s u$ forces $s' = s$, and (ii) every $x$ with $f(x^{-1}\gamma x) \neq 0$ can be written $x = t s u$ with $s \in S$, $t \in T$, $u \in U$. Then the number $\sum_{s \in S} f(s^{-1}\gamma s)/\tau\{t \in T : s^{-1} t s \in U\}$ is a value of the orbital integral of $f$ at $\gamma$ for the Haar measure on $\mathrm{GL}_2(K_v)$ normalising $U$ to mass $1$ and for $\tau$: that is, there exists $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$ which is nonnegative, measurable, of compact support, with $\int_T w(tx)\,d\tau(t) = 1$ for every $x$ such that $f(x^{-1}\gamma x) \neq 0$, and for which this sum equals $\int_{\mathrm{GL}_2(K_v)} f(x^{-1}\gamma x) w(x)\,dx$.
--
--   This is the standard evaluation of a local orbital integral of a bi-$\mathrm{GL}_2(\mathcal{O}_v)$-invariant function as a finite sum over representatives of the double cosets $T \backslash \mathrm{GL}_2(K_v) / \mathrm{GL}_2(\mathcal{O}_v)$ meeting the support of the conjugation orbit, the denominators being the volumes of the compact open stabilisers. It is used in the local comparison of orbital integrals at an inert prime and in the identification of an orbital integral in the case of irreducible characteristic polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem
AutomorphicForm.isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ AutomorphicForm.localIntegralSet K v, ∀ u₂ ∈ AutomorphicForm.localIntegralSet K v,
        f (u₁ * g * u₂) = f g)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ f
      (∑ s ∈ S, f (s⁻¹ * γ * s) /
        ((τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈
            AutomorphicForm.localIntegralSet K v}).toReal : ℂ)) := by sorry
