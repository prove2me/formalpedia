-- Prove2me | Theorems.Thm_CPDETrial_lemma_ec4
-- name    : CPDETrial.lemma_ec4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:44.751987+00:00
-- url     : https://prove2.me/theorems/64d45451-0ab2-4b1d-be00-85c334c4f652
-- title:
--   Lemma EC.4 — convergence of the cPDE index
-- statement:
--   Let $M\ge2$, $\Sigma^0$ positive definite, $\lambda>0$, $c>0$, and fix any allocation sequence and observation sequence and an arm $i$.
--
--   1. If arm $i$ is sampled infinitely often, then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$.
--   2. If $\lim_{T\to\infty}\Sigma^T_{i,i}=0$, then
--   $$
--   \lim_{T\to\infty}\nu^*_i(\mu^T,\Sigma^T)=-1 .
--   $$
--
--   Differences from the source:
--   - reading: no quantifier over sample paths → for every allocation and observation sequence (pathwise); reason: both halves hold pathwise, which implies the statement along every realization
--   - reading: lim_{T→∞} ν*_i(µ^t,Σ^t) → lim_{T→∞} ν*_i(µ^T,Σ^T); reason: the limit variable is T; µ^t is a typo
--   - reading: three formulas for ν* ((15) p. 11, (20) p. 12, (EC.8) p. ec3); p. 12 refers to '(19)' → ν* is (EC.8) with Δ = 1, as `nuStar`; reason: (EC.8) is the index the proof of Theorem 1 uses; (15) lacks −(1/c_i) max_j µ_j, with which Theorem 1(ii) fails; (20) agrees with (EC.8) only for deterministic T; '(19)' is the stopping index, a typo for (20); 'setting Δ = 0' on p. ec3 is a typo for Δ = 1
--   - reading: sup over T_i ≥ 1 for policies sampling only arm i → sup over stopping times T ≥ 1 of the natural filtration of Z with T < ∞ a.s., E[T] < ∞ and integrable payoff; reason: these are the policies of Π_i; a stopping time with E[T] = ∞ has value −∞ and does not attain the supremum
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec7, Lemma EC.4

import Mathlib
import Definitions.Def_CPDETrial_postMean
import Definitions.Def_CPDETrial_postCov
import Definitions.Def_CPDETrial_nuStar
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Lemma EC.4 — convergence of the cPDE index.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Lemma EC.4, p. ec7:
"If arm `i` is sampled infinitely often, then `lim_{T→∞} Σ^T_{i,i} = 0`. In turn, if
`lim_{T→∞} Σ^T_{i,i} = 0`, then `lim_{T→∞} ν*_i(µ^t,Σ^t) = −1` as well."

For `M ≥ 2`, `Σ⁰` positive definite, `λ > 0`, `c > 0`, every allocation sequence `u`, every
observation sequence `y` and every arm `i`:
1. if `u t = i` for infinitely many `t`, then `Σ^T_{ii} → 0`;
2. if `Σ^T_{ii} → 0`, then `ν*_i(µ^T, Σ^T) → −1`.

**Formalization Note.** Stated pathwise (for every allocation and observation sequence). The
page's `ν*_i(µ^t,Σ^t)` under `lim_{T→∞}` is read as `ν*_i(µ^T,Σ^T)`. -/
theorem lemma_ec4 {M : ℕ} (hM : 2 ≤ M) (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (lam : Fin M → ℝ≥0) (hlam : ∀ i, 0 < lam i) (c : Fin M → ℝ) (hc : ∀ j, 0 < c j)
    (u : ℕ → Fin M) (y : ℕ → ℝ) (i : Fin M) :
    ({t | u t = i}.Infinite →
      Tendsto (fun T => postCov Sig0 lam u T i i) atTop (𝓝 0)) ∧
    (Tendsto (fun T => postCov Sig0 lam u T i i) atTop (𝓝 0) →
      Tendsto (fun T => nuStar c lam i (postMean mu0 Sig0 lam u y T) (postCov Sig0 lam u T))
        atTop (𝓝 (-1))) := by sorry

end CPDETrial
