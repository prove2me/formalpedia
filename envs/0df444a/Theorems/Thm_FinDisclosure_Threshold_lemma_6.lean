-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_lemma_6
-- name    : FinDisclosure.Threshold.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:22.750542+00:00
-- url     : https://prove2.me/theorems/693215ca-b2a2-4f73-bcba-98af93161052
-- title:
--   Lemma 6, p. 38 — if E_µ0 c < I (and I < c(1)), some q̄ ∈ (0,1) bounds the feasible q, and ŝ(q̄) makes (20) bind
-- statement:
--   Assume the standing assumptions of the model, $\mathbb E_{\mu_0} c(s) < I$, and $I < c(1)$. Then there is $\bar q \in (0,1)$ such that
--
--   1. for every $q \in (\bar q, 1]$ the relaxed problem (31) has no feasible point, and
--   2. the cutoff $\hat s(\bar q)$, defined by $\int_{\hat s(\bar q)}^1 \mu_0(s)\,ds = \bar q$, solves
--   $$\int_{\hat s(\bar q)}^1 \big(c(s) - I\big)\,\mu_0(s)\,ds = 0.$$
--
--   Together with Lemma 5 this identifies $\bar q$ as the optimal probability of financing, at which the financing constraint binds.
--
--   **Formalization Note** The hypothesis $I < c(1)$ is not in the paper. Without it nothing can be financed, and there is no $\bar q \in (0,1)$ to speak of: if $c(1) < I$, problem (31) is infeasible for every $q > 0$. The case $q = 1$ is included, as in the text ("For $q = 1$, the entrepreneur's problem … does not admit a solution"). Clause 2 holds for every $t \in [0,1]$ with $\int_t^1 \mu_0 = \bar q$; the support assumption makes such a $t$ unique. No hypothesis $\lambda I \le B$ is needed.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 38 (PDF 38), Lemma 6; proof pp. 38–39 (PDF 38–39)

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Lemma 6, p. 38 (with the added hypothesis `I < c(1)`): if `E_{µ0} c(s) < I`, there is
`q̄ ∈ (0, 1)` such that the relaxed problem (31) is infeasible for every `q ∈ (q̄, 1]`, and the cutoff
`ŝ(q̄)` (defined by `∫_{ŝ(q̄)}^1 µ0 = q̄`) solves `∫_{ŝ(q̄)}^1 (c(s) - I) µ0(s) ds = 0`. -/
theorem lemma_6 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I) (hc1 : I < c 1) :
    ∃ qbar : ℝ, 0 < qbar ∧ qbar < 1 ∧
      (∀ q : ℝ, qbar < q → q ≤ 1 → ¬ ∃ m : ℝ → ℝ, Feas31 c f0 I q m) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∫ s in t..1, f0 s = qbar → ∫ s in t..1, (c s - I) * f0 s = 0 := by sorry

end FinDisclosure.Threshold
