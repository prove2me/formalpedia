-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen
-- name    : AutomorphicForm.exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/fcec0a85-e4e5-59ee-98f5-2ff997905b3e
-- title:
--   Level-U coset formula for local orbital integrals
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of $\mathcal{O}_K$, and write $G=\mathrm{GL}_2(K_v)$ for the general linear group over the completion $K_v$. Let $\gamma\in G$ be regular semisimple in the sense that $(\mathrm{tr}\,\gamma)^2-4\det\gamma$ is a unit, let $T=\mathrm{Subgroup.centralizer}\,\{\gamma\}$ carry its Borel $\sigma$-algebra, and let $\tau$ be a Haar measure on $T$. Let $U\le G$ be a subgroup which is open and contained in the set of $g\in G$ such that both $g$ and $g^{-1}$ have all entries in the valuation ring $\mathcal{O}_v$, and let $f:G\to\mathbb{C}$ be locally constant with compact support and satisfy $f(u_1gu_2)=f(g)$ for all $g\in G$, $u_1,u_2\in U$. The conclusion has two parts. First, there is a finite set $S\subseteq G$ whose elements are pairwise inequivalent for the $(T,U)$-action (if $s,s'\in S$ and $s'=tsu$ with $t\in T$, $u\in U$, then $s'=s$) and which covers the support of $x\mapsto f(x^{-1}\gamma x)$, i.e. $f(x^{-1}\gamma x)\neq 0$ implies $x\in TsU$ for some $s\in S$. Second, for every finite $S$ with these two properties, the number $$\sum_{s\in S} f(s^{-1}\gamma s)\,\frac{\mu(U)}{\tau(\{t\in T: s^{-1}ts\in U\})},$$ with $\mu$ the Haar measure on $G$ normalised to give mass $1$ to the above integral set and both measures taken in their real-valued form, is an orbital integral of $f$ at $\gamma$ relative to $\tau$: there exists $w:G\to\mathbb{R}$ nonnegative, measurable and compactly supported with $\int_T w(tx)\,d\tau(t)=1$ whenever $f(x^{-1}\gamma x)\neq 0$, such that the displayed sum equals $\int_G f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$.
--
--   This is the level-$U$ form of the coset-counting formula for orbital integrals of bi-$U$-invariant test functions on $\mathrm{GL}_2$ of a non-archimedean local field, the case $U=\mathrm{GL}_2(\mathcal{O}_v)$ being the count of $\gamma$-fixed vertices of the Bruhat–Tits tree. It is obtained from the general measure-theoretic section-function construction [`MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists`](thm.html#MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists) together with the finiteness of the relevant double cosets for regular semisimple $\gamma$, and it is used to evaluate orbital integrals of indicator functions of the integral set intersected with a principal congruence subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ]
    (U : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUo : IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))))
    (hU : (U : Set (GL (Fin 2) (v.adicCompletion K))) ⊆ AutomorphicForm.localIntegralSet K v)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hfU : ∀ g : GL (Fin 2) (v.adicCompletion K), ∀ u₁ ∈ U, ∀ u₂ ∈ U, f (u₁ * g * u₂) = f g) :
    (∃ S : Finset (GL (Fin 2) (v.adicCompletion K)),
      (∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ AutomorphicForm.localCentralizer K v γ, ∀ u ∈ U, s' = t * s * u → s' = s) ∧
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ AutomorphicForm.localCentralizer K v γ, ∃ u ∈ U, x = t * s * u) ∧
    ∀ S : Finset (GL (Fin 2) (v.adicCompletion K)),
      (∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ AutomorphicForm.localCentralizer K v γ, ∀ u ∈ U, s' = t * s * u → s' = s) →
      (∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ AutomorphicForm.localCentralizer K v γ, ∃ u ∈ U, x = t * s * u) →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f
        (letI := AutomorphicForm.localGLBorel K v
         ∑ s ∈ S, f (s⁻¹ * γ * s) *
            ((AutomorphicForm.localHaar K v (U : Set (GL (Fin 2) (v.adicCompletion K)))).toReal : ℂ) /
          ((τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈
              (U : Set (GL (Fin 2) (v.adicCompletion K)))}).toReal : ℂ)) := by sorry
