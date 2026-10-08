-- Prove2me | Theorems.Thm_ExecCompLP_Consistency_consistency
-- name    : ExecCompLP.Consistency.consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:26:12.300843+00:00
-- url     : https://prove2.me/theorems/4a72e27a-b55b-437e-9275-e087ae194aed
-- title:
--   §8 Appendix, p. 150 — under (I), (II) and nondegeneracy of α̂, the LP estimate â(η) → α̂ in probability
-- statement:
--   Let $\xi=(\xi_{ij})$ be a real $m\times n$ matrix of population means, $b\in\mathbb R^m$ and $c\in\mathbb R^n$. Assume
--
--   1. (I) the program $\min\sum_j c_j\alpha_j$ subject to $\sum_j\xi_{ij}\alpha_j\ge b_i$, $\alpha_j\ge0$ has a unique solution vector $\hat\alpha$;
--   2. (II) every set of $m$ columns of $\xi$ is linearly independent;
--   3. (added) $\hat\alpha$ is nondegenerate: the number of positive $\hat\alpha_j$ plus the number of constraints with $\sum_j\xi_{ij}\hat\alpha_j>b_i$ equals $m$.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space and, for each sample size $N$, let $\eta^{(N)}=(\eta^{(N)}_{ij})$ be a random $m\times n$ matrix of sampling errors with $\eta^{(N)}_{ij}\to0$ in probability as $N\to\infty$ for every $i,j$; the sample matrix is $x_{ij}=\xi_{ij}+\eta^{(N)}_{ij}$, as in (9). Then the estimates are consistent: for every $\varepsilon>0$,
--
--   $$P\Bigl(\text{(8) with matrix } \xi+\eta^{(N)} \text{ does not have a unique minimizing solution } \hat a \text{ with } \max_j|\hat a_j-\hat\alpha_j|<\varepsilon\Bigr)\longrightarrow0\qquad(N\to\infty).$$
--
--   In words: with probability tending to one the sample program (8) has exactly one minimizing solution $\hat a(\eta)$, and $\hat a(\eta)\to\hat\alpha$ in probability. This is the consistency claim of the Appendix of Charnes, Cooper and Ferguson, which justifies estimating the weights of an executive compensation scheme from sample ratings by linear programming.
--
--   **Formalization Note** The paper states the result under (I) and (II) alone; as printed it is false (see the companion `printed_statement_counterexample`), and the nondegeneracy of the true optimum $\hat\alpha$ is the single hypothesis added to repair it. Assumption (II) is kept as on the page although the repaired argument does not use it. The convergence $\eta\to0$ in probability is taken as the hypothesis (it is what (9) derives from the law of large numbers, called the central limit theorem on the page); sample means and variances are not modelled. The event above need not be measurable; $P$ of it is the outer measure, which is the stronger reading of "in probability", so no measurability of the estimator is assumed. Distances use the maximum norm on $\mathbb R^n$.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 150, §8, assumptions (I), (II) and the consistency claim; (8), (9) on p. 149

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

open MeasureTheory Filter Topology

namespace ExecCompLP.Consistency

theorem consistency {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (αhat : Fin n → ℝ) (hI : AssumptionI ξ b c αhat) (hII : AssumptionII ξ)
    (hnd : Nondegenerate ξ b αhat)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → Matrix (Fin m) (Fin n) ℝ)
    (hη : ∀ i j, TendstoInMeasure P (fun N ω => η N ω i j) atTop (fun _ => 0)) :
    ∀ ε > 0, Tendsto (fun N => P {ω | ¬ ∃ a, IsMinimizer (ξ + η N ω) b c a ∧
        (∀ a', IsMinimizer (ξ + η N ω) b c a' → a' = a) ∧ dist a αhat < ε})
      atTop (𝓝 0) := by sorry

end ExecCompLP.Consistency
