-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_a_7
-- name    : AMPLowDeg.RankOne.lemma_a_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:31.044386+00:00
-- url     : https://prove2.me/theorems/6078a9d2-43e0-4baa-9b2d-42c20fac34e5
-- title:
--   Lemma A.7 — the Bayes AMP value
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite. The infimum defining $q_{\mathrm{AMP}}$ in (1.3) is attained, and
--
--   $$
--   0<(\mathbb E[\Theta])^2\le q_{\mathrm{AMP}}\le m_2.
--   $$
--
--   Moreover, $q_{\mathrm{AMP}}$ is the smallest nonnegative fixed point of $F$. With $s=q_{\mathrm{AMP}}$, $\eta=\eta_s$ and $H_1=s\Theta+\sqrt sZ$ for independent $\Theta\sim\pi$, $Z\sim\mathcal N(0,1)$:
--
--   1. $\mathbb E[\eta(H_1)^2]=q_{\mathrm{AMP}}$;
--   2. $\mathbb E[(\eta'(H_1))^2]\le1$.
--
--   The first identity calibrates the rooted-tree bound of Lemma 2.4; the second (scalar stability) controls the degree-two vertices in Lemma 6.3.
--
--   Differences from the source:
--
--   - encoding: H₁ of (4.2) under the law of (θ, Z) → H₁ = sΘ + √s Z for (Θ, Z) ∼ π ⊗ 𝒩(0, 1); reason: H₁ = sθ₁ + √s Z₁ has exactly this law and both expectations depend only on it
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 25, Lemma A.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma A.7, p. 25 — the Bayes AMP value: if `E[Θ] ≠ 0` and all moments are finite, the infimum
defining `q_AMP` in (1.3) is attained, `0 < (E Θ)² ≤ q_AMP ≤ m₂`, `q_AMP` is the smallest
nonnegative fixed point of `F`, and with `s = q_AMP`, `η = η_s`, `H₁ = sΘ + √s Z`:
(1) `E[η(H₁)²] = q_AMP`; (2) `E[(η′(H₁))²] ≤ 1`. -/
theorem lemma_a_7 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) :
    qAMP π ∈ qAMPSet π ∧
    0 < mean π ^ 2 ∧ mean π ^ 2 ≤ qAMP π ∧ qAMP π ≤ m2 π ∧
    IsLeast {q : ℝ | 0 ≤ q ∧ scalarF π q = q} (qAMP π) ∧
    ∫ p, (eta π (qAMP π) (qAMP π * p.1 + Real.sqrt (qAMP π) * p.2)) ^ 2
        ∂(π.prod (gaussianReal 0 1)) = qAMP π ∧
    ∫ p, (deriv (eta π (qAMP π)) (qAMP π * p.1 + Real.sqrt (qAMP π) * p.2)) ^ 2
        ∂(π.prod (gaussianReal 0 1)) ≤ 1 := by sorry

end AMPLowDeg.RankOne
