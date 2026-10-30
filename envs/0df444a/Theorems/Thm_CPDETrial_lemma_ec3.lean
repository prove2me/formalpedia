-- Prove2me | Theorems.Thm_CPDETrial_lemma_ec3
-- name    : CPDETrial.lemma_ec3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:17.469533+00:00
-- url     : https://prove2.me/theorems/1a7eff4f-499b-4e77-bec2-fb2eb4125c0f
-- title:
--   Lemma EC.3 — small cKG₁ indices force full learning
-- statement:
--   In the trial model ($\theta\sim N(\mu^0,\Sigma^0)$ with $\Sigma^0$ positive definite, observations $N(\theta_i,\lambda_i)$ with $\lambda_i>0$, costs $c_i>0$, $M\ge2$), let the allocation be any nonanticipating rule. Then almost surely: if
--
--   $$
--   \liminf_{T\to\infty}\nu^{cKG_1}_i(\mu^T,\Sigma^T)=-1\quad\text{for all } i,
--   $$
--
--   then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$ for all $i$.
--
--   Differences from the source:
--   - reading: no quantifier over sample paths → almost surely, for every nonanticipating allocation; reason: pathwise the lemma is false (M = 2, Σ⁰ = Λ = I, c = 1, u ≡ arm 1, y_t = t²: both cKG₁ indices → −1 while Σ^T_22 = 1); the source XFC argument is almost sure
--   - encoding: liminf_{T→∞} ν^{cKG_1}_i = −1 → for every δ > 0, ν^{cKG_1}_i < −1 + δ for infinitely many T; reason: ν^{cKG_1}_i ≥ −1 always, so the two are equivalent; avoids Lean's junk value of liminf for unbounded sequences
--   - encoding: Y^t_i | θ_i ∼ N(θ_i, λ_i), independent given θ → Y^t_i = θ_i + ε^t_i, errors independent N(0, λ_i) independent of θ; reason: same joint law
--   - generalization: nonanticipating policies H_t → M (p. 7) → allocations measurable in H_t ∨ 𝓖 for an external σ-algebra 𝓖 independent of (θ, ε); reason: covers random tie-breaking and random consideration sets; taking 𝓖 trivial gives the paper's policies
--   - encoding: E[max_j{µ_j + (Σ_ij/Σ_ii) Z^τ_i} | µ^t,Σ^t] → integral against gaussianReal 0 σ²_{Z^τ_i} (eq. (10)); reason: the conditional law of Z^τ_i given the belief is this Gaussian; same value
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec6, Lemma EC.3

import Mathlib
import Definitions.Def_CPDETrial_muT
import Definitions.Def_CPDETrial_SigT
import Definitions.Def_CPDETrial_nuKG
import Definitions.Def_CPDETrial_TrialModel
import Definitions.Def_CPDETrial_IsNonanticipating
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Lemma EC.3 — small cKG₁ indices force full learning.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Lemma EC.3, p. ec6:
"If `liminf_{T→∞} ν^{cKG_1}_i(µ^T,Σ^T) = −1` for all `i`, then `lim_{T→∞} Σ^T_{i,i} = 0` for all
`i` as well."

Under the trial model (`TrialModel`: `θ ∼ N(µ⁰, Σ⁰)`, independent `N(0, λ_i)` sampling errors,
external randomization independent of both) with `M ≥ 2`, `Σ⁰` positive definite, `λ > 0`,
`c > 0`, and for **any** nonanticipating allocation `u`: almost surely, if
`liminf_T ν^{cKG_1}_i(µ^T, Σ^T) = −1` for every arm `i`, then `Σ^T_{ii} → 0` for every arm `i`.

**Formalization Note.**
1. The lemma is stated almost surely; pathwise it is false (with `M = 2`, `Σ⁰ = Λ = I`, `c = 1`,
   `u ≡ 1` and observations `y_t = t²`, both cKG₁ indices tend to `−1` while `Σ^T_{22} = 1`).
2. `liminf … = −1` is encoded as "for every `δ > 0`, frequently `ν^{cKG_1}_i < −1 + δ`". Since
   `ν^{cKG_1}_i ≥ −1` always (Jensen), the two are equivalent, and the encoding avoids Lean's
   junk value of `liminf` for sequences that are not bounded. -/
theorem lemma_ec3 {M : ℕ} (hM : 2 ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (lam : Fin M → ℝ≥0) (hlam : ∀ i, 0 < lam i) (c : Fin M → ℝ) (hc : ∀ j, 0 < c j)
    (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ) (𝓖 : MeasurableSpace Ω)
    (u : ℕ → Ω → Fin M)
    (hmodel : TrialModel P mu0 Sig0 lam θ ε 𝓖) (hna : IsNonanticipating 𝓖 θ ε u) :
    ∀ᵐ ω ∂P, (∀ i, ∀ δ : ℝ, 0 < δ → ∃ᶠ T in atTop,
        nuKG c lam 1 i (muT mu0 Sig0 lam θ ε u T ω) (SigT Sig0 lam u T ω) < -1 + δ) →
      ∀ i, Tendsto (fun T => SigT Sig0 lam u T ω i i) atTop (𝓝 0) := by sorry

end CPDETrial
