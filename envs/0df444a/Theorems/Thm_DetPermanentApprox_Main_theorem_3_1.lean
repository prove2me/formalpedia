-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_theorem_3_1
-- name    : DetPermanentApprox.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:23.3072+00:00
-- url     : https://prove2.me/theorems/f81c20ed-64d0-438a-98d3-c9547f586d72
-- title:
--   Theorem 3.1 — Convex rational upper surrogate with construction costs
-- statement:
--   Let $G$ be any finite simple graph on $N\ge2$ vertices, rational $K\ge1$, and real $0<\eta\le1$. The explicitly constructed rational polynomial $U$ has degree at most $m=O(K\log(2K/\eta))$, is convex in logarithmic weights on $D_K$, and satisfies
--
--   $$0\le U(e^y)-\log Z_G(e^y)\le\eta N/2\qquad(y\in D_K).$$
--
--   One uniform finite program constructs its coefficient table in $N^{O(m)}$ arithmetic operations. For each fixed derivative order, another uniform program evaluates its value or any mixed logarithmic derivative at the supplied $w=e^y$ within $N^{O(m)}$ operations. The big-O constants are independent of the graph and input weights, and the degree constant is absolute. Empty edge sets use $U=0$. This retains every analytic and computational clause.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: arithmetic operations and comparisons with polynomial rational intermediate bit lengths → finite rational-literal real pointer programs, guarded divisions, explicit input/output layouts, and bounds on actual runs and traces; reason: each executed instruction has unit cost and no elementary-function or counting oracle is present; polynomial control overhead is absorbed in the source asymptotic bounds
--   - encoding: Taylor and surrogate polynomials and any fixed-order logarithmic derivatives → rational multivariate polynomials from recurrence (3.2) and iterated Euler derivative polynomials; reason: the recurrence and w_e partial_w_e operator are the source formulas and supply all mixed derivative values
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Theorem 3.1, p. 11 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_PolynomialComputation

namespace DetPermanentApprox.Main

theorem theorem_3_1 :
    (∃ c : ℝ, 0 < c ∧ ∀ (N d : ℕ) (G : Graph (Fin N) (Fin d)), IsSimple G → 2 ≤ N →
      ∀ K : ℚ, 1 ≤ K → ∀ η : ℝ, 0 < η → η ≤ 1 →
      let m := truncationDegree K η
      let U := surrogate G K η
      (m : ℝ) ≤ c * (K : ℝ) * Real.log (2 * (K : ℝ) / η) ∧ U.totalDegree ≤ m ∧
      ConvexOn ℝ (degreeRegion G (K : ℝ)) (fun y => evaluate U (expWeights y)) ∧
      (∀ y ∈ degreeRegion G (K : ℝ),
        0 ≤ evaluate U (expWeights y) - Real.log (Z G (expWeights y)) ∧
        evaluate U (expWeights y) - Real.log (Z G (expWeights y)) ≤ η * N / 2)) ∧
    (∃ P : Program, RationalProgram P ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (N d : ℕ) (G : Graph (Fin N) (Fin d)), IsSimple G → 2 ≤ N →
      ∀ K : ℚ, 1 ≤ K → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ T : ℕ, validRun P (surrogateConstructionInput G K η) T ∧
        (T : ℝ) ≤ (N : ℝ) ^ (c * truncationDegree K η) ∧
        polynomialOutput (run P (surrogateConstructionInput G K η) T) (surrogate G K η)) ∧
    (∀ r : ℕ, ∃ P : Program, RationalProgram P ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (N d : ℕ) (G : Graph (Fin N) (Fin d)), IsSimple G → 2 ≤ N →
      ∀ K : ℚ, 1 ≤ K → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ (y : Fin d → ℝ) (edges : List (Fin d)), edges.length = r →
      ∃ T : ℕ, validRun P (surrogateEvaluationInput G K η (expWeights y) edges) T ∧
        (T : ℝ) ≤ (N : ℝ) ^ (c * truncationDegree K η) ∧
        output P (surrogateEvaluationInput G K η (expWeights y) edges) T =
          evaluate (logDerivativePolynomial (surrogate G K η) edges) (expWeights y)) := by sorry

end DetPermanentApprox.Main
