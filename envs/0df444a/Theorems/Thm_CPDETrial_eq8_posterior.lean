-- Prove2me | Theorems.Thm_CPDETrial_eq8_posterior
-- name    : CPDETrial.eq8_posterior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:38.466265+00:00
-- url     : https://prove2.me/theorems/305218e4-5ecc-4474-8779-a5202f5d2809
-- title:
--   Eq. (8) — the Gaussian posterior
-- statement:
--   1. **Block of samples.** From any belief $(\mu,\Sigma)$ with $\Sigma_{i,i}\ge0$ and $\lambda_i>0$, applying the one-observation update $\tau\ge1$ times to arm $i$ with observations $y_1,\dots,y_\tau$ gives
--   $$
--   \mu^{t+\tau}=\mu^t+\frac{\bar Y^\tau_i-\mu^t_i}{\lambda_i/\tau+\Sigma^t_{i,i}}\Sigma^te_i,\qquad \Sigma^{t+\tau}=\Sigma^t-\frac{\Sigma^te_ie_i^\top\Sigma^t}{\lambda_i/\tau+\Sigma^t_{i,i}},
--   $$
--   with $\bar Y^\tau_i=(y_1+\dots+y_\tau)/\tau$.
--   2. **Bayes' rule.** In the trial model with $\Sigma^0$ positive definite and $\lambda>0$, for any nonanticipating allocation, every time $t$ and every Borel set $B\subseteq\mathbb R^M$,
--   $$
--   \mathbb P(\theta\in B\mid\mathcal H_t)=N(\mu^t,\Sigma^t)(B)\quad\text{almost surely},
--   $$
--   where $(\mu^t,\Sigma^t)$ is computed by the recursion along the realized allocations and observations.
--
--   This is the inference the whole paper rests on: the belief $(\mu^t,\Sigma^t)$ is the exact posterior of $\theta$.
--
--   Differences from the source:
--   - generalization: posterior after τ samples from one arm, starting at time t → also the posterior given the history of any nonanticipating (adaptive) allocation, including external randomization 𝓖; reason: the consistency argument needs the adaptive case; a deterministic block of samples of arm i is a special case, and part 1 identifies its block formula with (8)
--   - generalization: (8) for a belief (µ^t, Σ^t) with Σ^t a covariance matrix → part 1 for any real M × M matrix S with S_ii ≥ 0 (no symmetry or positive semidefiniteness); reason: the block identity is algebraic and needs only positive denominators; posterior covariances satisfy S_ii ≥ 0
--   - encoding: Y^t_i | θ_i ∼ N(θ_i, λ_i), independent given θ → Y^t_i = θ_i + ε^t_i, errors independent N(0, λ_i) independent of θ; reason: same joint law
--   - encoding: posterior mean and covariance → the regular conditional probability of θ given H_t is N(µ^t, Σ^t), stated as a conditional expectation of indicators for each Borel set; reason: a Gaussian posterior is determined by its mean and covariance; same content
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 9, eq. (8)

import Mathlib
import Definitions.Def_CPDETrial_postMean
import Definitions.Def_CPDETrial_postCov
import Definitions.Def_CPDETrial_muT
import Definitions.Def_CPDETrial_SigT
import Definitions.Def_CPDETrial_hist
import Definitions.Def_CPDETrial_TrialModel
import Definitions.Def_CPDETrial_IsNonanticipating
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Eq. (8) — the Gaussian posterior.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.1, eq. (8), p. 9: "Bayes' rule provides the following posterior mean and covariance
(Frazier et al. 2009): `µ^{t+τ} = µ^t + (Ȳ^τ_i − µ^t_i)/(λ_i/τ + Σ^t_{i,i}) Σ^t e_i`, and
`Σ^{t+τ} = Σ^t − Σ^t e_i e_iᵀ Σ^t/(λ_i/τ + Σ^t_{i,i})`".

1. **(Block of `τ` samples.)** Starting from any belief `(m, S)` with `S_ii ≥ 0` and `λ_i > 0`,
   `τ ≥ 1` consecutive one-observation updates of arm `i` with observations `y_0, …, y_{τ−1}`
   give the `τ`-sample formula (8) with `Ȳ^τ_i = (y_0 + ⋯ + y_{τ−1})/τ`.
2. **(Bayes' rule.)** Under the trial model with `Σ⁰` positive definite and `λ > 0`, for any
   nonanticipating allocation `u`, every time `t` and every Borel set `B`, the conditional
   probability `P(θ ∈ B | H_t)` equals `N(µ^t, Σ^t)(B)` almost surely, where `(µ^t, Σ^t)` is the
   recursion (8) along the realized allocations and observations.

**Formalization Note.** Part 2 extends the paper's statement from a block of samples of one arm
to adaptively chosen arms (the form the consistency argument of XFC uses); for a deterministic
block of samples of arm `i` it gives the paper's (8) by part 1. `H_t` includes the external
randomization `𝓖` (`hist`). -/
theorem eq8_posterior {M : ℕ} :
    (∀ (lam : Fin M → ℝ≥0) (m : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
        (y : ℕ → ℝ) (τ : ℕ), 0 < lam i → 0 ≤ S i i → 1 ≤ τ →
      postMean m S lam (fun _ => i) y τ =
          m + ((((∑ r ∈ Finset.range τ, y r) / τ) - m i) / ((lam i : ℝ) / τ + S i i)) •
            (fun a => S a i) ∧
      postCov S lam (fun _ => i) τ =
          S - (1 / ((lam i : ℝ) / τ + S i i)) • Matrix.of (fun a b => S a i * S i b)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (mu0 : Fin M → ℝ) (Sig0 : Matrix (Fin M) (Fin M) ℝ) (lam : Fin M → ℝ≥0)
        (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ) (𝓖 : MeasurableSpace Ω)
        (u : ℕ → Ω → Fin M),
      Sig0.PosDef → (∀ i, 0 < lam i) →
      TrialModel P mu0 Sig0 lam θ ε 𝓖 → IsNonanticipating 𝓖 θ ε u →
      ∀ (t : ℕ) (B : Set (EuclideanSpace ℝ (Fin M))), MeasurableSet B →
        P[(θ ⁻¹' B).indicator (fun _ => (1 : ℝ)) | hist 𝓖 θ ε u t] =ᵐ[P]
          fun ω => (multivariateGaussian (WithLp.toLp 2 (muT mu0 Sig0 lam θ ε u t ω))
            (SigT Sig0 lam u t ω) B).toReal) := by sorry

end CPDETrial
