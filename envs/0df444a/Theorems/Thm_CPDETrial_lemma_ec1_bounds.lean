-- Prove2me | Theorems.Thm_CPDETrial_lemma_ec1_bounds
-- name    : CPDETrial.lemma_ec1_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:55:45.255821+00:00
-- url     : https://prove2.me/theorems/cd6f17bc-ca32-4a07-b62c-33e9539f33bd
-- title:
--   Lemma EC.1 — cKG bounds on the cPDE index (corrected: τ̄ = ⌈max_j Σ⁰_jj/(4 min_j c_j²)⌉, not (EC.11))
-- statement:
--   Let $M\ge2$, $\Sigma^0$ positive definite, $\lambda_j>0$ and $c_j>0$ for all $j$. Put
--
--   $$
--   \bar\tau=\left\lceil\frac{\max_j\Sigma^0_{j,j}}{4(\min_j c_j)^2}\right\rceil .
--   $$
--
--   Then for every allocation sequence and observation sequence, every time $t$ and every arm $i$, the posterior $(\mu^t,\Sigma^t)$ satisfies
--
--   $$
--   \nu^{cKG_1}_i(\mu^t,\Sigma^t)\le\nu^*_i(\mu^t,\Sigma^t)\le\nu^{cKG_{1:\bar\tau}}_i(\mu^t,\Sigma^t).
--   $$
--
--   The cPDE index is thus sandwiched between two cKG indices with a fixed lookahead, which is how its limits are obtained from those of the cKG indices.
--
--   Differences from the source:
--   - correction: τ̄ = ⌈√((2 min_j λ_j/π) · max_j Σ⁰_jj/min_j c_j)⌉ → τ̄ = ⌈max_j Σ⁰_jj/(4 (min_j c_j)²)⌉; reason: the printed value makes the upper bound false: M = 2, µ⁰ = 0, Σ⁰ = 0.01·I, Λ = I, c = (10⁻⁴, 10⁻⁴) give printed τ̄ = 8 and ν^{cKG_{1:8}}_1 ≈ 107.6, while T ≡ 75 gives ν*_1 ≥ 186.2
--   - reading: three formulas for ν* ((15) p. 11, (20) p. 12, (EC.8) p. ec3); p. 12 refers to '(19)' → ν* is (EC.8) with Δ = 1, as `nuStar`; reason: (EC.8) is the index the proof of Theorem 1 uses; (15) lacks −(1/c_i) max_j µ_j, with which Theorem 1(ii) fails; (20) agrees with (EC.8) only for deterministic T; '(19)' is the stopping index, a typo for (20); 'setting Δ = 0' on p. ec3 is a typo for Δ = 1
--   - reading: sup over T_i ≥ 1 for policies sampling only arm i → sup over stopping times T ≥ 1 of the natural filtration of Z with T < ∞ a.s., E[T] < ∞ and integrable payoff; reason: these are the policies of Π_i; a stopping time with E[T] = ∞ has value −∞ and does not attain the supremum
--   - encoding: E[max_j{µ_j + (Σ_ij/Σ_ii) Z^τ_i} | µ^t,Σ^t] → integral against gaussianReal 0 σ²_{Z^τ_i} (eq. (10)); reason: the conditional law of Z^τ_i given the belief is this Gaussian; same value
--   - reading: (µ^t, Σ^t), the belief at time t → the posterior (8) along any allocation and observation sequence; reason: the bounds depend on the data only through the belief; covers every realization of the trial
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec3, Lemma EC.1 (proof pp. ec3–ec6; τ̄ of eq. (EC.11), p. ec5, corrected)

import Mathlib
import Definitions.Def_CPDETrial_postMean
import Definitions.Def_CPDETrial_postCov
import Definitions.Def_CPDETrial_nuStar
import Definitions.Def_CPDETrial_nuKG
import Definitions.Def_CPDETrial_tauBar
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Lemma EC.1 — cKG bounds on the cPDE index (corrected `τ̄`).**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Lemma EC.1, p. ec3 (proof pp. ec3–ec6):
"Let `τ̄ = ⌈√((2 min_j{λ_j}/π) · max_j{Σ⁰_{j,j}}/min_j{c_j})⌉`. Then
`ν^{cKG_1}_i(µ^t,Σ^t) ≤ ν*_i(µ^t,Σ^t) ≤ ν^{cKG_{1:τ̄}}_i(µ^t,Σ^t)`."

For `M ≥ 2` arms, a positive definite prior covariance `Σ⁰`, positive sampling variances and
positive costs, along **every** allocation sequence `u` and observation sequence `y`, at every
time `t` and for every arm `i`, the posterior `(µ^t, Σ^t)` of (8) satisfies
`ν^{cKG_1}_i ≤ ν*_i ≤ ν^{cKG_{1:τ̄}}_i` with the corrected `τ̄ = ⌈max_j Σ⁰_{jj}/(4 (min_j c_j)²)⌉`.

**Formalization Note.** The printed `τ̄` makes the upper bound false (counterexample in
`tauBar`'s docstring); `tauBar` is the corrected horizon. The statement holds pathwise: the
indices depend on the data only through `(µ^t, Σ^t)`. -/
theorem lemma_ec1_bounds {M : ℕ} (hM : 2 ≤ M) (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (lam : Fin M → ℝ≥0) (hlam : ∀ i, 0 < lam i) (c : Fin M → ℝ) (hc : ∀ j, 0 < c j)
    (u : ℕ → Fin M) (y : ℕ → ℝ) (t : ℕ) (i : Fin M) :
    nuKG c lam 1 i (postMean mu0 Sig0 lam u y t) (postCov Sig0 lam u t) ≤
      nuStar c lam i (postMean mu0 Sig0 lam u y t) (postCov Sig0 lam u t) ∧
    nuStar c lam i (postMean mu0 Sig0 lam u y t) (postCov Sig0 lam u t) ≤
      nuKG c lam (tauBar Sig0 c) i (postMean mu0 Sig0 lam u y t) (postCov Sig0 lam u t) := by sorry

end CPDETrial
