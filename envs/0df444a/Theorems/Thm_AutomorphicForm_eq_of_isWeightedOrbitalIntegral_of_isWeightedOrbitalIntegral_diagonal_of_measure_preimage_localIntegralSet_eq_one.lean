-- Prove2me | Theorems.Thm_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
-- name    : AutomorphicForm.eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fb8eebbb-675a-52ba-85ca-0441e3999555
-- title:
--   Uniqueness of local weighted orbital integrals at diagonal elements
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of $\mathcal{O}_K$, and $\gamma \in \mathrm{GL}_2(K_v)$ an element of the group of units over the completion $K_v$ which is regular semisimple in the sense that $(\operatorname{tr}\gamma)^2 - 4\det\gamma$ is a unit of $K_v$, and which is diagonal: its $(0,1)$ and $(1,0)$ entries vanish. Let $\tau_1,\tau_2$ be two measures on the centraliser $Z = \mathrm{Cent}(\{\gamma\}) \le \mathrm{GL}_2(K_v)$, taken with its Borel $\sigma$-algebra, each a Haar measure, and each assigning mass $1$ to the set of points of $Z$ lying in [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), i.e. those $g$ with both $g$ and $g^{-1}$ having all entries in the valuation ring $\mathcal{O}_v$. Let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, that is locally constant with compact support, and let $J_1, J_2 \in \mathbb{C}$ be such that, for $i = 1,2$, there is a real-valued function $s$ on $\mathrm{GL}_2(K_v)$ satisfying the section predicate [`AutomorphicForm.IsSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L239) for the data $(\gamma, \tau_i, f)$ with $$J_i = \int_{\mathrm{GL}_2(K_v)} f(x^{-1}\gamma x)\, w(x)\, s(x)\, d\mu(x),$$ where $\mu$ is the normalised Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ and $w(x) = 2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot \mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$ is the local weight. Then $J_1 = J_2$.
--
--   This is the well-definedness statement for the local weighted orbital integral at a split (diagonal) regular semisimple element: the value is independent both of the choice of Haar measure on the centralising torus, once that measure is normalised to give the integral points mass one, and of the auxiliary section function occurring in the integral. It is used downstream in the comparison of weighted local integrals with class integrals and in the construction of test functions with prescribed weighted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (τ₁ τ₂ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (h₁ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ₁)
    (h₂ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ₂)
    (h₁1 : τ₁ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (h₂1 : τ₂ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (J₁ J₂ : ℂ) (hJ₁ : AutomorphicForm.IsWeightedOrbitalIntegral K v γ τ₁ f J₁)
    (hJ₂ : AutomorphicForm.IsWeightedOrbitalIntegral K v γ τ₂ f J₂) : J₁ = J₂ := by sorry
