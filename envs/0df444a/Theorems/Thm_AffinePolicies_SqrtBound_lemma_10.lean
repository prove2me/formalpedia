-- Prove2me | Theorems.Thm_AffinePolicies_SqrtBound_lemma_10
-- name    : AffinePolicies.SqrtBound.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:40:14.181612+00:00
-- url     : https://prove2.me/theorems/414c8ef8-eac8-4b9b-bdc9-c7eb71e77315
-- title:
--   Lemma 10, PDF p. 29 — Algorithm 𝒜 executes at most 2√m iterations
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^m$, let $\mu_j=\max\{b_j:b\in\mathcal U\}$ and assume $\mu_j>0$ for every $j$. If iterations $1,\dots,K$ of Algorithm $\mathcal A$ are executed (each with the loop test satisfied and a maximizing choice $u^k\in\mathcal U$), then
--   $$K\le 2\sqrt m .$$
--
--   In particular the number of iterations $K$ of a complete run is at most $2\sqrt m$, and the algorithm terminates. The bound is used in the proof of Theorem 4 to show that $2\sqrt m/K\ge1$.
--
--   **Formalization Note** The statement is made for every executed prefix of iterations, without the stopping test; this is stronger than the paper's statement about the number of iterations of a finished run, and it is what yields termination. Nonnegativity, convexity and compactness of $\mathcal U$ are not assumed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 10, PDF p. 29

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem lemma_10 {m : ℕ} (U : Set (Fin m → ℝ))
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by sorry

end AffinePolicies.SqrtBound
