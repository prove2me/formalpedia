-- Prove2me | Theorems.Thm_ConsistentSubmodular_finiteExpectation_card
-- name    : ConsistentSubmodular.finiteExpectation_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:59.530467+00:00
-- url     : https://prove2.me/theorems/50ad6bbc-6b6a-42d0-a2f8-679eb602b9b1
-- title:
--   Expected size of an independent random set is $\sum_e p_e$
-- statement:
--   Let $p=(p_e)_{e<n}$ be a vector of reals and let $S$ be the random subset of $\{0,\dots,n-1\}$ containing each $e$ independently with probability $p_e$, with expectation understood as the sum over all subsets $S$ of $\prod_{e\in S}p_e\prod_{e\notin S}(1-p_e)$ times the value at $S$. Then
--   $$\mathbb E\bigl[\,|S|\,\bigr]\;=\;\sum_{e<n}p_e .$$
--
--   This is linearity of expectation for the cardinality of an independent sample. It is used to control the expected size of the sampled core against the budget.
--
--   **Formalization Note**: no hypothesis $0\le p_e\le 1$ is required; the identity holds for the formal weighted sum for arbitrary real $p$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SamplingCardinality.lean#L14-L30 (`ConsistentSubmodular.finiteExpectation_card`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.finiteExpectation_card {n : ℕ} (p : Fin n → ℝ) :
    finiteExpectation p (fun S => (S.card : ℝ)) = ∑ e, p e := by sorry
