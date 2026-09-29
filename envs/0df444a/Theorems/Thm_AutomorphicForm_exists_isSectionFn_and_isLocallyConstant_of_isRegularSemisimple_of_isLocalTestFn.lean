-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
-- name    : AutomorphicForm.exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/1161efc1-e864-5f7c-813e-6cbd70c32d20
-- title:
--   Locally constant section functions at regular semisimple elements of GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and let $K_v$ denote the associated adic completion. Let $\gamma \in \mathrm{GL}_2(K_v)$ be regular semisimple in the sense used here, namely that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $K_v$ (equivalently, is nonzero). Write $T_\gamma = \mathrm{Cent}_{\mathrm{GL}_2(K_v)}(\{\gamma\})$ for the centraliser subgroup of $\gamma$, equipped with its Borel $\sigma$-algebra, and let $\tau$ be a Haar measure on $T_\gamma$. Let $f_v \colon \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, that is, locally constant with compact support. The assertion is that there exists a function $w \colon \mathrm{GL}_2(K_v) \to \mathbb{R}$ which is a section function for the data $(\gamma, \tau, f_v)$ and is in addition locally constant; being a section function means that $w$ is nonnegative everywhere, measurable for the Borel $\sigma$-algebra on $\mathrm{GL}_2(K_v)$, compactly supported, and satisfies $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ for every $x \in \mathrm{GL}_2(K_v)$ with $f_v(x^{-1}\gamma x) \neq 0$.
--
--   Section functions are the normalising weights used to define the local orbital integral $\int f_v(x^{-1}\gamma x)\,w(x)\,dx$ of a local test function at a regular semisimple element; this statement supplies one that is moreover locally constant, for an arbitrary Haar measure on the centraliser. It is used in the local matching statements for test functions and Hecke operators, for instance in the comparison of orbital and twisted orbital integrals at a prime. The proof cites [`MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one`](thm.html#MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one), the general existence of such a weight along a closed commutative subgroup relative to a compact set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

theorem AutomorphicForm.exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ]
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
      AutomorphicForm.IsSectionFn K v γ τ fv w ∧ IsLocallyConstant w := by sorry
