-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_eq_2_1
-- name    : AMPLowDeg.RankOne.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:35.054328+00:00
-- url     : https://prove2.me/theorems/0b309b22-3e58-47ac-b188-1492178c8149
-- title:
--   §2, eq. (2.1) — variational formula for $\mathrm{MMSE}_{\le D}$
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, let $n\ge1$, $D\ge0$, and let $(\theta,Y)$ follow model (1.1). Then $\mathrm{MMSE}_{\le D}$ is finite and
--
--   $$
--   \mathrm{MMSE}_{\le D}=m_2-\sup_{\substack{\deg f\le D\\ \mathbb E[f(Y)^2]>0}}\frac{\mathbb E[\theta_1f(Y)]^2}{\mathbb E[f(Y)^2]},
--   $$
--
--   where $f$ ranges over real polynomials of total degree at most $D$ in $(Y_e)_{e\in\mathcal E_n}$, and the supremum (of a nonempty set bounded above) exists.
--
--   The formula reduces the vector estimation problem to the correlation of a single scalar polynomial with $\theta_1$; every lower bound in the paper bounds this supremum.
--
--   Differences from the source:
--
--   - encoding: MMSE_{≤D} = m₂ − sup{…} → ∃ S, IsLUB {…} S ∧ mmseLD π n D ≠ ⊤ ∧ (mmseLD π n D).toReal = m₂ − S; reason: a real supremum is stated through IsLUB (so its existence is asserted, not a junk sSup); MMSE_{≤D} lives in [0, ∞] and is asserted finite
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 6, §2, eq. (2.1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- §2, eq. (2.1), p. 6 — the variational formula
`MMSE_{≤D} = m₂ − sup_{deg f ≤ D, E[f(Y)²] > 0} E[θ₁ f(Y)]² / E[f(Y)²]`. The supremum exists
(as a least upper bound), `MMSE_{≤D}` is finite, and the identity holds. Vertex `1` is `⟨0, hn⟩`. -/
theorem eq_2_1 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n D : ℕ) (hn : 0 < n) :
    ∃ S : ℝ, IsLUB {q : ℝ | ∃ f : MvPolynomial (Edge n) ℝ, f.totalDegree ≤ D ∧
        0 < ∫ w, (MvPolynomial.eval (obs w.1 w.2) f) ^ 2 ∂(modelLaw π n) ∧
        q = (∫ w, w.1 ⟨0, hn⟩ * MvPolynomial.eval (obs w.1 w.2) f ∂(modelLaw π n)) ^ 2 /
          ∫ w, (MvPolynomial.eval (obs w.1 w.2) f) ^ 2 ∂(modelLaw π n)} S ∧
      mmseLD π n D ≠ ⊤ ∧ (mmseLD π n D).toReal = m2 π - S := by sorry

end AMPLowDeg.RankOne
