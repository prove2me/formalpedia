-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
-- name    : AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/0ea13729-5a4a-51d9-9762-e5a41dacb822
-- title:
--   Existence of local orbital integrals at regular semisimple elements
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime ideal of its ring of integers $\mathcal{O}_K$, and let $K_v$ denote the associated completion. Let $\gamma \in \mathrm{GL}_2(K_v)$ satisfy [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), i.e. $(\operatorname{tr}\gamma)^2 - 4\det\gamma$ is a unit of $K_v$, hence nonzero. Write $T_\gamma$ for the centralizer subgroup of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$, equipped with its Borel $\sigma$-algebra, and let $\tau$ be a Haar measure on $T_\gamma$. Let $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be locally constant with compact support. Then there exists $I \in \mathbb{C}$ which is an orbital integral of $f_v$ at $\gamma$ against $\tau$ in the sense of [`AutomorphicForm.IsOrbitalIntegral`](def/AutomorphicForm_LocalOrbitalBase.html#L208): there is a function $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$ that is nonnegative, Borel measurable and compactly supported, satisfies $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ for every $x$ with $f_v(x^{-1}\gamma x) \neq 0$, and for which $I = \int_{\mathrm{GL}_2(K_v)} f_v(x^{-1}\gamma x)\, w(x)$ against the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ normalised to give mass $1$ to the compact set [`AutomorphicForm.localIntegralCompacts K v`](def/AutomorphicForm_LocalOrbitalBase.html#L120). The substance is the existence of the weight function $w$, the number $I$ being then given by the displayed integral.
--
--   This is the basic existence statement for local orbital integrals of locally constant compactly supported test functions at a regular semisimple element of $\mathrm{GL}_2$ over a non-archimedean completion, in the form used throughout the project: the orbital integral is realised by a compactly supported weight function which integrates to $1$ along the orbits of the centralizer over the relevant part of the support. It is invoked by the later comparisons of local and archimedean orbital integrals, by the computations of orbital and twisted orbital integrals attached to Hecke operators, and by the matching statements relating these to Satake data; the existence of the weight function itself is supplied by [`MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one`](thm.html#MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

theorem AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ]
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ fv I := by sorry
