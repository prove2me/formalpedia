-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_lemma_1
-- name    : CorreaThreshold.Nonadaptive.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:48.842342+00:00
-- url     : https://prove2.me/theorems/72545c99-63a7-4f59-9ecd-19bbe13dca28
-- title:
--   Lemma 1, p. 1455 — Bernoulli Selection Lemma
-- statement:
--   Let $Y_i$ be independent Bernoulli indicators with success probabilities $q_i\in[0,1]$, and let $b_i\in\mathbb R$ be fixed prizes. For a deterministic subset $S$, its reward is the average of the successful prizes in $S$, with value zero if none succeeds. Let $P^*$ be the maximum expected reward over all $S$.
--
--   For every vector $0\le z_i\le q_i$ with $\sum_i z_i\le1$, and for some such vector $z$, respectively, the two inequalities are
--
--   $$P^*\ge(1-1/e)\sum_i b_i z_i,\qquad \sum_i b_i z_i\ge\mathbb E\!\left[\max_i b_iY_i\right].$$
--
--   These are the two links in the paper's displayed chain of maxima. The lemma supplies the subset used in the proof of Theorem 1.
--
--   **Formalization Note** $n\ge1$ and indices are 0-based. The lower bound $z_i\ge0$ is implicit in the paper: the variables are probabilities, and allowing negative values makes the optimization unbounded for negative prizes. The finite maximum avoids an ill-defined real supremum.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1455, Lemma 1; p. 1456, (3); https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

namespace CorreaThreshold.Nonadaptive

/-- The two inequalities of the Bernoulli Selection Lemma. -/
theorem lemma_1 {n : ℕ} [NeZero n] (q b : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ q i) →
      (∑ i, z i) ≤ 1 →
      (1 - Real.exp (-1)) * (∑ i, b i * z i) ≤ objP q b) ∧
    (∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ q i) ∧
      (∑ i, z i) ≤ 1 ∧
      bernExp q (fun T => Finset.univ.sup' Finset.univ_nonempty
        (fun i => if i ∈ T then b i else 0)) ≤ ∑ i, b i * z i) := by sorry

end CorreaThreshold.Nonadaptive
