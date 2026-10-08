-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_theorem_5_1
-- name    : ArapostathisAC.VanishingDiscount.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:41:45.527427+00:00
-- url     : https://prove2.me/theorems/d290e4f9-c331-4bd2-bc2f-c2c65e16f9f2
-- title:
--   Theorem 5.1 — ACOE solutions with (5.2) characterize the optimal average cost and average optimal stationary policies
-- statement:
--   Consider the countable-state controlled Markov process of §5. Let $(\rho,h)$ be a solution of the average cost optimality equation
--   $$\rho+h(i)=\min_{a\in U(i)}\Big\{c(i,a)+\sum_{j\in S}P(j\mid i,a)h(j)\Big\},\qquad i\in S,\tag{5.1}$$
--   and assume that for every admissible policy $\pi\in\Pi$ and every initial state $i$, $h(X_t)$ is $P^\pi_i$-integrable for every $t$ and
--   $$\lim_{t\to\infty}\frac1t E^\pi_i h(X_t)=0.\tag{5.2}$$
--   Then:
--
--   1. $\rho\ge 0$ and there is $f\in\Pi_{SD}$ with $\rho=J(i,f)=J^*(i)$ for all $i\in S$;
--   2. every $f\in\Pi_{SD}$ that selects a minimizer in (5.1) at every state, i.e.
--   $$c(i,f(i))+\sum_{j\in S}P(j\mid i,f(i))h(j)=\min_{a\in U(i)}\Big\{c(i,a)+\sum_{j\in S}P(j\mid i,a)h(j)\Big\}\quad\forall i\in S,\tag{5.3}$$
--   is average optimal;
--   3. conversely, if $f\in\Pi_{SD}$ is average optimal and its state chain is irreducible and positive recurrent, then $f$ satisfies (5.3).
--
--   The theorem is the verification theorem of the average cost problem: a solution of the ACOE with the growth condition (5.2) identifies the optimal average cost and the optimal stationary policies.
--
--   **Formalization Note.** The paper prints (5.2) "for all $\pi\in\Pi_{SD}$", but its conclusion $\rho=J^*(i)$ is an infimum over all admissible policies, and the proof applies (5.2) to an arbitrary policy $\pi$ ("if $\pi$ is any other policy, we can show using the same arguments …", p. 300). We state (5.2) for every $\pi\in\Pi$, which makes the hypothesis stronger than printed. $E^\pi_i h(X_t)$ is a Bochner integral, so its integrability is part of the hypothesis. A solution of the ACOE requires every series $\sum_jP(j\mid i,a)h(j)$, $a\in U(i)$, to converge and the minimum to be attained; the paper leaves the convergence implicit. $J(i,f)$ and $J^*(i)$ are $[0,\infty]$-valued, so "$\rho=J(i,f)=J^*(i)$" is stated as an equality in $[0,\infty]$ with $\rho$ embedded by `ENNReal.ofReal`, together with the separate conclusion $\rho\ge0$, so that no sign is assumed silently. (5.3) is stated as "$f(i)$ attains the minimum", which is equivalent since $f(i)\in U(i)$. $J^*$ is the infimum over all history-dependent randomized policies.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 299, Theorem 5.1, (5.1)–(5.3); proof pp. 299–300

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain

open MeasureTheory Filter Topology

namespace ArapostathisAC.VanishingDiscount

theorem theorem_5_1 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hsol : ACOE M ρ h)
    (h52 : ∀ π : Policy M, ∀ i,
      (∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i)) ∧
      Tendsto (fun t : ℕ => (∫ ω, h (ω t).1 ∂(pathMeasure M π i)) / t) atTop (𝓝 0)) :
    (0 ≤ ρ ∧ ∃ f : StationaryPolicy M, ∀ i,
        avgCost M f.toPolicy i = ENNReal.ofReal ρ ∧ optAvg M i = ENNReal.ofReal ρ) ∧
    (∀ f : StationaryPolicy M,
      (∀ i, ∀ a ∈ M.U i, M.c i (f.1 i) + ∑' j, prob M i (f.1 i) j * h j ≤
        M.c i a + ∑' j, prob M i a j * h j) → IsAvgOptimal M f) ∧
    (∀ f : StationaryPolicy M, IsAvgOptimal M f → IsIrreducible M f → IsPositiveRecurrent M f →
      ∀ i, ∀ a ∈ M.U i, M.c i (f.1 i) + ∑' j, prob M i (f.1 i) j * h j ≤
        M.c i a + ∑' j, prob M i a j * h j) := by sorry

end ArapostathisAC.VanishingDiscount
