-- Prove2me | Theorems.Thm_AuditAdapt_Supplement_theorem_5_4
-- name    : AuditAdapt.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:38:41.777233+00:00
-- url     : https://prove2.me/theorems/a7677564-04d4-4546-bece-b1c95298e07d
-- title:
--   Theorem 5.4, p.5 — lower bound: auditing needs $T\ge\frac{9}{2048}(\Gamma+1)\ln(1/(4\eta))/\delta^2$ when $\bar\chi^2(\pi)=\Gamma$
-- statement:
--   In the contextual-bandit auditing problem of §5.1 (see Theorem 5.3), for every
--
--   $$
--   \Gamma\ge\tfrac13,\qquad \delta\in(0,\tfrac1{32}],\qquad \eta\in(0,\tfrac18],
--   $$
--
--   there is a context distribution $\mathcal D$ and a policy $\pi$ with $\bar\chi^2(\pi)=\Gamma$, together with two cost models (cost laws with values in $[0,1]^{\mathcal A}$), such that every auditor that is $(\delta,\eta)$-accurate on both instances requires
--
--   $$
--   T\ \ge\ \frac{9}{2048}\cdot\frac{(\Gamma+1)\ln\!\big(1/(4\eta)\big)}{\delta^2}.
--   $$
--
--   Here an auditor is any (measurable) function of the $T$-round log $\{(x_t,\pi(\cdot\mid x_t),a_t,\ell_t(a_t))\}_{t=1}^T$; it may use the known $\pi$ and $\bar p$, which are the same in both instances. Together with Theorem 5.3 this shows that $\bar\chi^2(\pi)$ is the right complexity parameter for auditing the adaptivity cost: the upper bound $O(\bar\chi^2\log(1/\eta)/\delta^2)$ is matched up to constants for every value $\bar\chi^2\ge1/3$.
--
--   **Formalization Note** The Lean statement holds on every measurable context space with measurable singletons and at least two points and every finite action set with at least two actions, which includes the instance of the proof ($\mathcal X=\{0,1\}$, $\mathcal A=\{1,2\}$). Policies and cost models are Markov kernels.
--
--   Differences from the source:
--   - encoding: policy π(· | x) ∈ Δ(A), measurable in x → Markov kernel πk : Kernel X A, π(a | x) = (πk x {a}).toReal; reason: a measurable family of distributions on a finite set is a Markov kernel; same instances
--   - encoding: conditional cost law with mean c(x), ℓ ∈ [0, 1]^A → Markov kernel K : Kernel X (A → ℝ) with K(x)-a.s. ℓ ∈ [0, 1]^A for every x, c(x)(a) = ∫ ℓ(a) dK(x); reason: same instances
--   - encoding: x_t ∼ D i.i.d.; ℓ_t and a_t independent given x_t → T-round law Measure.pi of D ⊗ₘ (K ×ₖ πk); reason: the composition-product with the product kernel is conditional independence given x
--   - generalization: there is a context distribution D (on a context space and with an action set the proof chooses: X = {0, 1}, A = {1, 2}) → for every measurable space X with measurable singletons and at least two points and every finite A with at least two actions, there are D and π; reason: taking X = Fin 2, A = Fin 2 gives the source's existence claim
--   - reading: every auditor (a function of the T-round log) → every measurable function f of the T-round log {(x_t, π(· | x_t), a_t, ℓ_t(a_t))}, which may depend on the fixed D, π and p̄; reason: the success probability P(|Δ̂ − Δ(π)| < δ) in the definition of accuracy is defined only for a measurable output
--   - encoding: χ̄²(π) = Γ → chiBar D πk = ENNReal.ofReal Γ; reason: Γ ≥ 1/3 > 0, so ofReal is exact
--   - encoding: P(|Δ̂ − Δ(π)| < δ) ≥ 1 − η on each instance → ENNReal.ofReal (1 − η) ≤ (measure of the event under the T-round law of that instance); reason: η ≤ 1/8, so ofReal(1 − η) = 1 − η
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Theorem 5.4 (Lower bound), p.5 (PDF p.5), with the setting of §5.1, p.5

import Mathlib
import Definitions.Def_AuditAdapt_Supplement_chiSq
import Definitions.Def_AuditAdapt_Supplement_banditAdaptivityCost
import Definitions.Def_AuditAdapt_Supplement_banditRoundLaw

namespace AuditAdapt.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 5.4 (Lower bound), p.5** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). For every `Γ ≥ 1/3`, `δ ∈ (0, 1/32]` and
`η ∈ (0, 1/8]`, there is a context distribution `D` and a policy `π` with `χ̄²(π) = Γ`, together with two
cost models, such that every auditor that is `(δ, η)`-accurate on both instances requires
`T ≥ (9/2048) · (Γ + 1) ln(1/(4η)) / δ²`.

An auditor is a measurable function `f` of the `T`-round log `{(x_t, π(· | x_t), a_t, ℓ_t(a_t))}_{t≤T}`
(`banditLog`); it may depend on `p̄` and `π`, which are fixed before `f` is chosen. It is
`(δ, η)`-accurate on the instance with cost model `K` if `P(|f(log) − Δ(π)| < δ) ≥ 1 − η` under the `T`-round
law of that instance, where `Δ(π) = banditAdaptivityCost D πk K`.

**Formalization Note** The statement is proved for every measurable context space `X` with measurable
singletons and at least two points and every finite action set `A` with at least two actions; the
paper's instance (`X = {0,1}`, `A = {1,2}`) is one such choice, so this specializes to the paper's
existence claim. Cost models are Markov kernels `K : Kernel X (A → ℝ)` with costs in `[0,1]^A` almost
surely. `χ̄²(π) = Γ` holds exactly, in `ℝ≥0∞`. The auditor's measurability is what makes its success
probability defined. -/
theorem theorem_5_4 {X A : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Nontrivial X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nontrivial A]
    (Γ δ η : ℝ) (hΓ : 1 / 3 ≤ Γ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 32) (hη0 : 0 < η) (hη1 : η ≤ 1 / 8) :
    ∃ (D : Measure X) (πk : Kernel X A), IsProbabilityMeasure D ∧ IsMarkovKernel πk ∧
      chiBar D πk = ENNReal.ofReal Γ ∧
      ∃ K₁ K₂ : Kernel X (A → ℝ), IsMarkovKernel K₁ ∧ IsMarkovKernel K₂ ∧
        (∀ x, ∀ᵐ ℓ ∂(K₁ x), ∀ a, ℓ a ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ x, ∀ᵐ ℓ ∂(K₂ x), ∀ a, ℓ a ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ (T : ℕ) (f : (Fin T → X × (A → ℝ) × A × ℝ) → ℝ), Measurable f →
          ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin T => banditRoundLaw D πk K₁)
              {ω | |f (fun t => banditLog πk (ω t)) - banditAdaptivityCost D πk K₁| < δ} →
          ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin T => banditRoundLaw D πk K₂)
              {ω | |f (fun t => banditLog πk (ω t)) - banditAdaptivityCost D πk K₂| < δ} →
          9 / 2048 * ((Γ + 1) * Real.log (1 / (4 * η))) / δ ^ 2 ≤ (T : ℝ) := by sorry

end AuditAdapt.Supplement
