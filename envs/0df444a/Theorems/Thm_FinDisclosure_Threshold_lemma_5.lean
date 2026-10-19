-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_lemma_5
-- name    : FinDisclosure.Threshold.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:28.002796+00:00
-- url     : https://prove2.me/theorems/b8bfd28f-5e55-44c9-b5f5-7ed9e2a7907a
-- title:
--   Lemma 5, p. 38 (monotonicity part) — V(q) is strictly increasing in q where F(q) is nonempty (with λI ≤ B)
-- statement:
--   Assume the standing assumptions of the model and $\lambda I \le B$. Let $V(q)$ be the value of problem (30),
--   $$V(q) = \sup\Big\{ q\int_0^1 \big(s - c(s) + B + \lambda(c(s) - I)\big)\mu_h(s)\,ds \;:\; \mu_h \text{ feasible for (30)} \Big\}.$$
--   If $0 < q < q' < 1$ and problem (30) is feasible at $q'$, then
--   $$V(q) < V(q').$$
--
--   So the entrepreneur wants to make the probability that the project is financed as large as the financing constraint allows. This is the part of Lemma 5 that the proof of Proposition 1 uses.
--
--   **Formalization Note** Feasibility at $q$ is not assumed: it follows from feasibility at $q' > q$. The hypothesis $\lambda I \le B$ is not in the paper, and the claim fails without it. With $\mu_0 = 1$, $c(s) = s$, $I = 0.6$, $B = 0.1$ and $\lambda = 1$, the value of (30) at $q = 0.5$ is $0.125$, larger than its value $0.08$ at $q = 0.8$. Continuity and differentiability of $V$, the other claims of Lemma 5, are not formalized.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 38 (PDF 38), Lemma 5 and its proof

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Lemma 5, p. 38, monotonicity part (with the added hypothesis `λ I ≤ B`): the value `V(q)` of
problem (30) is strictly increasing in `q` on `(0, 1)` wherever the larger problem is feasible. -/
theorem lemma_5 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam) (hB : lam * I ≤ B)
    (q q' : ℝ) (hq0 : 0 < q) (hqq' : q < q') (hq'1 : q' < 1)
    (hfeas : ∃ m : ℝ → ℝ, Feas30 c f0 I q' m) :
    V c f0 I B lam q < V c f0 I B lam q' := by sorry

end FinDisclosure.Threshold
