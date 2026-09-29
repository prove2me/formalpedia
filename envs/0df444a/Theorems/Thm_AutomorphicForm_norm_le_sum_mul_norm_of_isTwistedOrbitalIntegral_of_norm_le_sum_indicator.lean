-- Prove2me | Theorems.Thm_AutomorphicForm_norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
-- name    : AutomorphicForm.norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/26df9766-9040-5505-bd96-6cd2e344587e
-- title:
--   Domination of twisted orbital integrals by weighted indicators
-- statement:
--   Let $K \subseteq L$ be number fields, $v$ a nonzero prime of $\mathcal{O}_K$, and write $E_v = L \otimes_K K_v$ for the tensor product of $L$ with the completion of $K$ at $v$. Let $\sigma$ be a $K$-automorphism of $L$ with $\sigma^{[L:K]} = 1$, inducing by base change the endomorphism `sigmaGL` of $\mathrm{GL}_2(E_v)$, and let $\delta \in \mathrm{GL}_2(E_v)$ be such that its norm string $\prod_{i=0}^{[L:K]-1} \sigma^i(\delta)$ (the ordered product of the iterates of `sigmaGL` applied to $\delta$) is regular semisimple in the sense that $(\operatorname{tr} g)^2 - 4\det g$ is a unit of $E_v$. Let $\tau'$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta$, and let $\varphi_v : \mathrm{GL}_2(E_v) \to \mathbb{C}$ be locally constant with compact support. Assume given a finite index set $s \subseteq \iota$, sets $U_i \subseteq \mathrm{GL}_2(E_v)$ that are open and compact for $i \in s$, reals $c_i \ge 0$ for $i \in s$, and the pointwise bound $\|\varphi_v(g)\| \le \sum_{i \in s} c_i \mathbf{1}_{U_i}(g)$ for all $g$. If $I \in \mathbb{C}$ is a value of the twisted orbital integral of $\varphi_v$ at $(\delta, \tau')$ against the semi-local Haar measure, namely $I = \int \varphi_v(x^{-1}\delta\,\sigma(x))\,w(x)\,d\mu(x)$ for some twisted section function $w$, and $J_i \in \mathbb{C}$ are such values for the indicator functions $\mathbf{1}_{U_i}$, $i \in s$, then $\|I\| \le \sum_{i \in s} c_i \|J_i\|$.
--
--   This is the comparison step in the local analysis of twisted orbital integrals at a regular semisimple norm string: any test function dominated by a finite nonnegative combination of compact open indicators has its twisted orbital integral dominated by the same combination of the corresponding indicator integrals. It is used in establishing uniform bounds for twisted orbital integrals of semi-local test functions, and relies on the independence of the twisted orbital integral from the choice of section function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (ι : Type) (s : Finset ι) (U : ι → Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hUo : ∀ i ∈ s, IsOpen (U i)) (hUc : ∀ i ∈ s, IsCompact (U i))
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hle : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ‖φv g‖ ≤ ∑ i ∈ s, c i * (U i).indicator (fun _ => (1 : ℝ)) g)
    (I : ℂ) (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I)
    (J : ι → ℂ)
    (hJ : ∀ i ∈ s, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' ((U i).indicator (fun _ => (1 : ℂ))) (J i)) :
    ‖I‖ ≤ ∑ i ∈ s, c i * ‖J i‖ := by sorry
