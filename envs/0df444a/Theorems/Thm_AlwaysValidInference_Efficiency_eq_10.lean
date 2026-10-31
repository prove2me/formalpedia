-- Prove2me | Theorems.Thm_AlwaysValidInference_Efficiency_eq_10
-- name    : AlwaysValidInference.Efficiency.eq_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:41:22.446831+00:00
-- url     : https://prove2.me/theorems/360162ed-1ca2-469e-bd9f-dbc43cebbf4d
-- title:
--   Section 5.2, equation (10) — normalized mSPRT stopping time
-- statement:
--   Fix any observation model and mixing distribution from Sections 3 and 5.2, and any fixed $\theta\in\Theta\setminus\{\theta_0\}$. With
--   $$I(\theta,\theta_0)=(\theta-\theta_0)\psi'(\theta)-(\psi(\theta)-\psi(\theta_0)),$$
--   the untruncated mSPRT satisfies
--   $$\frac{T^H(\alpha)}{\log(1/\alpha)}\longrightarrow I(\theta,\theta_0)^{-1}\qquad(\alpha\downarrow0),$$
--   both in probability and in $L^2$ under $P_\theta$. The stopping times are almost surely finite and the normalized times have finite second moment. Both assertions are conclusions; no runtime bound or asymptotic limit is assumed. This is the entire equation (10), retaining the full positive continuous-density class of fixed mixtures.
--
--   Differences from the source:
--   - generalization: density f₀(x) exp(θx − ψ(θ)) with respect to Lebesgue measure → exp(θx − ψ(θ)) with respect to an arbitrary reference measure; reason: taking reference = f₀ dx recovers every source family without any added assumption
--   - reading: equation (7) writes the density quotient at the sample mean → the exponential likelihood ratio after cancelling the common carrier; reason: this is the intended likelihood ratio, agreeing wherever the quotient is defined; I3 records a source-admissible support where the printed quotient is 0/0
--   - encoding: observations indexed from one and positive integer stopping times with possible infinity → observation index zero is X₁; times lie in ℕ∞ with positivity imposed; reason: the first n coordinates are exactly the first n samples and the empty crossing set remains infinity
--   - encoding: convergence in probability and in L² as α tends to zero → right-neighborhood limits of tail probabilities and nonnegative squared-error integrals, with measurability, finite second moments and almost-sure finiteness in the conclusion; reason: these express the two original convergence modes without converting infinite stopping times to zero
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, §5.2, equation (10), p. 19 (PDF page = printed page).

import Definitions.Def_AlwaysValidInference_Efficiency_StoppingLimit

namespace AlwaysValidInference.Efficiency

theorem eq_10 {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (H : MixingDistribution E.family.domain) (θ : ℝ)
    (hθ : θ ∈ E.family.domain) (hne : θ ≠ E.null) :
    StoppingLimit E H θ := by sorry

end AlwaysValidInference.Efficiency
