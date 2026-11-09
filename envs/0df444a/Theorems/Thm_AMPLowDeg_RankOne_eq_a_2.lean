-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_eq_a_2
-- name    : AMPLowDeg.RankOne.eq_a_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:25.663365+00:00
-- url     : https://prove2.me/theorems/0911a083-08a0-4314-b3fc-c0fe8c42e5f4
-- title:
--   §A.4, eq. (A.2) — I–MMSE and MMSE-derivative identities
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, let $I_\pi(s)=I(\Theta;\sqrt s\Theta+Z)$ (in nats), and $F(s)=\mathbb E[\eta_s(H)^2]$ with $H=s\Theta+\sqrt sZ$, $F(0)=(\mathbb E\Theta)^2$. Then
--
--   $$
--   I_\pi'(s)=\tfrac12\big(m_2-F(s)\big),\qquad F'(s)=\mathbb E\big[\eta_s'(s\Theta+\sqrt sZ)^2\big],\qquad s>0,
--   $$
--
--   where $\eta_s'$ is the derivative in the field variable. Moreover $F$ is infinitely differentiable on $(0,\infty)$ and continuous at $0$ from the right with value $(\mathbb E\Theta)^2$, and the first identity holds at $s=0$ for the right derivative: $I_\pi'(0^+)=\tfrac12(m_2-(\mathbb E\Theta)^2)$.
--
--   These are the I–MMSE identity and the MMSE-derivative identity of the scalar Gaussian channel; substituted into $\Psi$ they give $\Psi'(q)=\tfrac12(q-F(q))$ and $\Psi''(q)=\tfrac12(1-F'(q))$, which locate $q_{\mathrm{AMP}}$ in Lemma A.7.
--
--   Differences from the source:
--
--   - encoding: F continuous at zero; right derivative of I_π at 0 → ContinuousWithinAt F [0, ∞) 0 and HasDerivWithinAt I_π … [0, ∞) 0; reason: F and I_π are functions on [0, ∞); one-sided limits are limits within [0, ∞)
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 24, §A.4, eq. (A.2) and the regularity sentences after it; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace AMPLowDeg.RankOne

/-- §A.4, eq. (A.2), p. 24 — the I–MMSE and MMSE-derivative identities with their regularity:
for `s > 0`, `I′_π(s) = (m₂ − F(s))/2` and `F′(s) = E[η′_s(sΘ + √s Z)²]`; `F` is smooth on
`(0, ∞)` and continuous at `0` from the right with `F(0) = (E Θ)²`; and the first identity holds
for the right derivative at `0`. Mutual information is in nats. -/
theorem eq_a_2 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) :
    (∀ s : ℝ, 0 < s → HasDerivAt (MI π) ((m2 π - scalarF π s) / 2) s) ∧
    (∀ s : ℝ, 0 < s → HasDerivAt (scalarF π)
      (∫ p, (deriv (eta π s) (s * p.1 + Real.sqrt s * p.2)) ^ 2 ∂(π.prod (gaussianReal 0 1))) s) ∧
    ContDiffOn ℝ ∞ (scalarF π) (Set.Ioi 0) ∧
    ContinuousWithinAt (scalarF π) (Set.Ici 0) 0 ∧
    HasDerivWithinAt (MI π) ((m2 π - scalarF π 0) / 2) (Set.Ici 0) 0 := by sorry

end AMPLowDeg.RankOne
