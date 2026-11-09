-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_3_2
-- name    : DetPermanentApprox.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:20.735626+00:00
-- url     : https://prove2.me/theorems/641d6663-bcd9-485b-ad11-96f409ae4f75
-- title:
--   Lemma 3.2 — Rational Taylor polynomial and evaluation costs
-- statement:
--   Let $G$ be any finite simple graph on $N\ge2$ vertices, fix rational $K\ge1$, and let $m\ge1$. The recurrence-defined polynomial $T_m(w)$ has rational coefficients and degree at most $m$. Uniform finite programs construct its coefficient table and, given $w=e^y$, evaluate its value and every fixed-order mixed derivative in logarithmic weights, with
--
--   $$\text{arithmetic cost}\le N^{c_r m}.$$
--
--   The constant may depend on the derivative order $r$ and is uniform over the graph, weights, $K$ and $m$; the order-zero derivative is the value. This retains both construction and evaluation clauses for general simple graphs, including graphs with no edges.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: arithmetic operations and comparisons with polynomial rational intermediate bit lengths → finite rational-literal real pointer programs, guarded divisions, explicit input/output layouts, and bounds on actual runs and traces; reason: each executed instruction has unit cost and no elementary-function or counting oracle is present; polynomial control overhead is absorbed in the source asymptotic bounds
--   - encoding: Taylor and surrogate polynomials and any fixed-order logarithmic derivatives → rational multivariate polynomials from recurrence (3.2) and iterated Euler derivative polynomials; reason: the recurrence and w_e partial_w_e operator are the source formulas and supply all mixed derivative values
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 3.2, p. 12 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_PolynomialComputation

namespace DetPermanentApprox.Main

theorem lemma_3_2 :
    (∀ (N d : ℕ) (G : Graph (Fin N) (Fin d)), IsSimple G → 2 ≤ N →
      ∀ (K : ℚ), 1 ≤ K → ∀ m : ℕ, 1 ≤ m →
        (taylorPolynomial G K m).totalDegree ≤ m) ∧
    (∃ P : Program, RationalProgram P ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (N d : ℕ) (G : Graph (Fin N) (Fin d)), IsSimple G → 2 ≤ N →
      ∀ (K : ℚ), 1 ≤ K → ∀ m : ℕ, 1 ≤ m →
      ∃ T : ℕ, validRun P (taylorConstructionInput G K m) T ∧
        (T : ℝ) ≤ (N : ℝ) ^ (c * m) ∧
        polynomialOutput (run P (taylorConstructionInput G K m) T) (taylorPolynomial G K m)) ∧
    (∀ r : ℕ, ∃ P : Program, RationalProgram P ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (N d : ℕ) (G : Graph (Fin N) (Fin d)), IsSimple G → 2 ≤ N →
      ∀ (K : ℚ), 1 ≤ K → ∀ m : ℕ, 1 ≤ m →
      ∀ (y : Fin d → ℝ) (edges : List (Fin d)), edges.length = r →
      ∃ T : ℕ, validRun P (evaluationInput G K m (expWeights y) edges) T ∧
        (T : ℝ) ≤ (N : ℝ) ^ (c * m) ∧
        output P (evaluationInput G K m (expWeights y) edges) T =
          evaluate (logDerivativePolynomial (taylorPolynomial G K m) edges) (expWeights y)) := by sorry

end DetPermanentApprox.Main
