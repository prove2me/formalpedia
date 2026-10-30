-- Prove2me | Theorems.Thm_CPDETrial_lemma_ec5
-- name    : CPDETrial.lemma_ec5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:22:55.020871+00:00
-- url     : https://prove2.me/theorems/f8709358-b0de-4a11-b05f-bc8160802067
-- title:
--   Lemma EC.5 — small cPDE indices force full learning
-- statement:
--   In the trial model ($\theta\sim N(\mu^0,\Sigma^0)$ with $\Sigma^0$ positive definite, observations $N(\theta_i,\lambda_i)$ with $\lambda_i>0$, costs $c_i>0$, $M\ge2$), let the allocation be any nonanticipating rule. Then almost surely: if
--
--   $$
--   \liminf_{T\to\infty}\nu^*_i(\mu^T,\Sigma^T)=-1\quad\text{for all } i,
--   $$
--
--   then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$ for all $i$.
--
--   Differences from the source:
--   - reading: no quantifier over sample paths → almost surely, for every nonanticipating allocation; reason: pathwise the lemma is false (same example as Lemma EC.3)
--   - reading: lim_{T→∞} ν*_i(µ^t,Σ^t) → lim_{T→∞} ν*_i(µ^T,Σ^T); reason: the limit variable is T; µ^t is a typo
--   - encoding: liminf_{T→∞} ν*_i = −1 → for every δ > 0, ν*_i < −1 + δ for infinitely many T; reason: ν*_i ≥ −1 always, so the two are equivalent; avoids Lean's junk value of liminf for unbounded sequences
--   - encoding: Y^t_i | θ_i ∼ N(θ_i, λ_i), independent given θ → Y^t_i = θ_i + ε^t_i, errors independent N(0, λ_i) independent of θ; reason: same joint law
--   - generalization: nonanticipating policies H_t → M (p. 7) → allocations measurable in H_t ∨ 𝓖 for an external σ-algebra 𝓖 independent of (θ, ε); reason: covers random tie-breaking and random consideration sets; taking 𝓖 trivial gives the paper's policies
--   - reading: three formulas for ν* ((15) p. 11, (20) p. 12, (EC.8) p. ec3); p. 12 refers to '(19)' → ν* is (EC.8) with Δ = 1, as `nuStar`; reason: (EC.8) is the index the proof of Theorem 1 uses; (15) lacks −(1/c_i) max_j µ_j, with which Theorem 1(ii) fails; (20) agrees with (EC.8) only for deterministic T; '(19)' is the stopping index, a typo for (20); 'setting Δ = 0' on p. ec3 is a typo for Δ = 1
--   - reading: sup over T_i ≥ 1 for policies sampling only arm i → sup over stopping times T ≥ 1 of the natural filtration of Z with T < ∞ a.s., E[T] < ∞ and integrable payoff; reason: these are the policies of Π_i; a stopping time with E[T] = ∞ has value −∞ and does not attain the supremum
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec7, Lemma EC.5

import Mathlib
import Definitions.Def_CPDETrial_muT
import Definitions.Def_CPDETrial_SigT
import Definitions.Def_CPDETrial_nuStar
import Definitions.Def_CPDETrial_TrialModel
import Definitions.Def_CPDETrial_IsNonanticipating
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Lemma EC.5 — small cPDE indices force full learning.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Lemma EC.5, p. ec7:
"If `liminf_{T→∞} ν*_i(µ^t,Σ^t) = −1` for all `i`, then `lim_{T→∞} Σ^T_{i,i} = 0` for all `i` as
well."

Under the trial model with `M ≥ 2`, `Σ⁰` positive definite, `λ > 0`, `c > 0`, and for **any**
nonanticipating allocation `u`: almost surely, if `liminf_T ν*_i(µ^T, Σ^T) = −1` for every arm
`i`, then `Σ^T_{ii} → 0` for every arm `i`.

**Formalization Note.**
1. Stated almost surely (pathwise it is false; see `lemma_ec3`). The page's `ν*_i(µ^t,Σ^t)` is
   read as `ν*_i(µ^T,Σ^T)`.
2. `liminf … = −1` is encoded as "for every `δ > 0`, frequently `ν*_i < −1 + δ`", equivalent
   because `ν*_i ≥ ν^{cKG_1}_i ≥ −1`. -/
theorem lemma_ec5 {M : ℕ} (hM : 2 ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (lam : Fin M → ℝ≥0) (hlam : ∀ i, 0 < lam i) (c : Fin M → ℝ) (hc : ∀ j, 0 < c j)
    (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ) (𝓖 : MeasurableSpace Ω)
    (u : ℕ → Ω → Fin M)
    (hmodel : TrialModel P mu0 Sig0 lam θ ε 𝓖) (hna : IsNonanticipating 𝓖 θ ε u) :
    ∀ᵐ ω ∂P, (∀ i, ∀ δ : ℝ, 0 < δ → ∃ᶠ T in atTop,
        nuStar c lam i (muT mu0 Sig0 lam θ ε u T ω) (SigT Sig0 lam u T ω) < -1 + δ) →
      ∀ i, Tendsto (fun T => SigT Sig0 lam u T ω i i) atTop (𝓝 0) := by sorry

end CPDETrial
