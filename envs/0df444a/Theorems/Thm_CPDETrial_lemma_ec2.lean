-- Prove2me | Theorems.Thm_CPDETrial_lemma_ec2
-- name    : CPDETrial.lemma_ec2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:20:10.19379+00:00
-- url     : https://prove2.me/theorems/bd65cb9b-fca0-4947-baa1-82af7d4ea237
-- title:
--   Lemma EC.2 — convergence of the cKG upper bound
-- statement:
--   Let $M\ge2$, $\Sigma^0$ positive definite, $\lambda>0$, $c>0$, and fix any allocation sequence and observation sequence and an arm $i$.
--
--   1. If arm $i$ is sampled infinitely often, then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$.
--   2. If $\lim_{T\to\infty}\Sigma^T_{i,i}=0$, then for every fixed lookahead $\tau\ge1$,
--   $$
--   \lim_{T\to\infty}\nu^{cKG_{1:\tau}}_i(\mu^T,\Sigma^T)=-1 .
--   $$
--
--   In the paper the lookahead is $\bar\tau$ of Lemma EC.1.
--
--   Differences from the source:
--   - generalization: the lookahead τ̄ of Lemma EC.1 → every fixed lookahead τ ≥ 1; reason: τ̄ (printed or corrected) is one such τ
--   - reading: no quantifier over sample paths → for every allocation and observation sequence (pathwise); reason: both halves hold pathwise, which implies the statement along every realization
--   - encoding: E[max_j{µ_j + (Σ_ij/Σ_ii) Z^τ_i} | µ^t,Σ^t] → integral against gaussianReal 0 σ²_{Z^τ_i} (eq. (10)); reason: the conditional law of Z^τ_i given the belief is this Gaussian; same value
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec6, Lemma EC.2

import Mathlib
import Definitions.Def_CPDETrial_postMean
import Definitions.Def_CPDETrial_postCov
import Definitions.Def_CPDETrial_nuKG
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Lemma EC.2 — convergence of the cKG upper bound.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Lemma EC.2, p. ec6:
"If arm `i` is sampled infinitely often, then `lim_{T→∞} Σ^T_{i,i} = 0`. In turn, if
`lim_{T→∞} Σ^T_{i,i} = 0`, then `lim_{T→∞} ν^{cKG_{1:τ̄}}_i(µ^T,Σ^T) = −1` as well."

For `M ≥ 2`, `Σ⁰` positive definite, `λ > 0`, `c > 0`, every allocation sequence `u`, every
observation sequence `y` and every arm `i`:
1. if `u t = i` for infinitely many `t`, then `Σ^T_{ii} → 0`;
2. for every lookahead `τ ≥ 1`, if `Σ^T_{ii} → 0` then `ν^{cKG_{1:τ}}_i(µ^T, Σ^T) → −1`.

**Formalization Note.** Stated pathwise, for every allocation and observation sequence, which
implies the statement along every realization of the trial. Part 2 is stated for every fixed
`τ ≥ 1`; the paper's `τ̄` (printed or corrected) is one such `τ`. -/
theorem lemma_ec2 {M : ℕ} (hM : 2 ≤ M) (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (lam : Fin M → ℝ≥0) (hlam : ∀ i, 0 < lam i) (c : Fin M → ℝ) (hc : ∀ j, 0 < c j)
    (u : ℕ → Fin M) (y : ℕ → ℝ) (i : Fin M) :
    ({t | u t = i}.Infinite →
      Tendsto (fun T => postCov Sig0 lam u T i i) atTop (𝓝 0)) ∧
    ∀ τ : ℕ, 1 ≤ τ → Tendsto (fun T => postCov Sig0 lam u T i i) atTop (𝓝 0) →
      Tendsto (fun T => nuKG c lam τ i (postMean mu0 Sig0 lam u y T) (postCov Sig0 lam u T))
        atTop (𝓝 (-1)) := by sorry

end CPDETrial
