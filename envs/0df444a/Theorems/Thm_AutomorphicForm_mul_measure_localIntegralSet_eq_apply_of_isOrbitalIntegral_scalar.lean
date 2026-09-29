-- Prove2me | Theorems.Thm_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
-- name    : AutomorphicForm.mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a148b708-a305-5db3-bac8-ece3be808c25
-- title:
--   Orbital integral at a scalar in GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of $\mathcal O_K$, with completion $K_v$ and valuation ring $\mathcal O_v$. Let $\gamma \in \mathrm{GL}_2(K_v)$ and assume $\gamma = c \cdot 1$ is the scalar matrix attached to some unit $c$ of $K_v$. Let $\tau$ be a measure on the centraliser subgroup $T_\gamma = \mathrm{Subgroup.centralizer}\,\{\gamma\}$ of $\mathrm{GL}_2(K_v)$, taken with its Borel $\sigma$-algebra [`AutomorphicForm.localCentralizerBorel`](def/AutomorphicForm_LocalOrbitalBase.html#L197), and assume $\tau$ is a (left) Haar measure. Let $f_v \colon \mathrm{GL}_2(K_v) \to \mathbb C$ be an arbitrary function and $I \in \mathbb C$ a value of the orbital-integral relation [`AutomorphicForm.IsOrbitalIntegral`](def/AutomorphicForm_LocalOrbitalBase.html#L208) for $f_v$ at $\gamma$ relative to $\tau$: there is $w \colon \mathrm{GL}_2(K_v) \to \mathbb R$ which is nonnegative, Borel measurable and compactly supported, satisfies $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ for every $x$ with $f_v(x^{-1}\gamma x) \neq 0$, and for which $I = \int_{\mathrm{GL}_2(K_v)} f_v(x^{-1}\gamma x)\,w(x)\,d\mu_v(x)$, where $\mu_v$ is the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$. Then $I$ times the real number $\tau\bigl(\{t \in T_\gamma : t \in \mathrm{GL}_2(\mathcal O_v)\}\bigr)$, viewed as a complex number, equals $f_v(\gamma)$. Here $\mathrm{GL}_2(\mathcal O_v)$ means [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g$ whose matrix and whose inverse matrix both have all entries in $\mathcal O_v$.
--
--   This is the degenerate case of the local orbital integral at a central element, where the centraliser is the whole group and the orbital integral collapses to the value of $f_v$ divided by the measure of $\mathrm{GL}_2(\mathcal O_v)$; it records the normalisation of the two Haar measures involved. It is used in the comparison of twisted and ordinary orbital integrals at scalar elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ∃ c : (v.adicCompletion K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v γ τ fv I) :
    letI := AutomorphicForm.localCentralizerBorel K v γ
    I * ((τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal : ℂ) =
      fv γ := by sorry
