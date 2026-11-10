-- Prove2me | Theorems.Thm_CNFLearnMQ_corollary_4_4
-- name    : CNFLearnMQ.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:32.11378+00:00
-- url     : https://prove2.me/theorems/af5a03fb-c8a7-409d-a9be-8ac8c84ad1a1
-- title:
--   Corollary 4.4 — antichain, size and intersection bounds for $\mathcal R_X$
-- statement:
--   Let $\Phi=(V,C)$ be a CNF formula on $n$ variables with $m=|C|\ge1$ nonempty clauses, each of width at most $k$, in which every variable occurs in at most $d$ clauses (the standing assumptions of §4, p.15).
--   For every solution $X$ of $\Phi$:
--
--   1. $\mathcal R_X$ is an antichain: if $R_1\subseteq R_2$ are cores then $R_1=R_2$.
--   2. $|\mathcal R_X|\le m\le nd$ and $1\le|R|\le k$ for every core $R$; if every clause has width $k$, then $m\le nd/k$.
--   3. Each core $R$ intersects at most $dk$ cores of $\mathcal R_X$.
--
--   These bounds control the running time of LearnCore (item 2), the success probability of its iterations (items 1 and 3, used in Lemma 4.8), and the degree of the core dependency graph.
--
--   Differences from the source:
--   - reading: each core intersects at most $dk$ cores in $\mathcal R_X$ → the cores $R'$ with $R'\cap R\ne\emptyset$, $R$ itself included, number at most $dk$; reason: the proof counts every core whose witness clause meets $R$, which includes $R$; this is the stronger of the two readings
--   - encoding: $m\le nd/k$ → $(m:\mathbb R)\le nd/k$ over the reals; reason: the quotient is real; same instances
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Corollary 4.4, p.17

import Mathlib
import Definitions.Def_CNFLearnMQ_cores

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Corollary 4.4, p.17 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §4 (p.15: `m = |C| ≥ 1`
nonempty clauses, each of width at most `k`, maximum variable degree at most `d`), for any
solution `X`:
1. `R_X` is an antichain;
2. `|R_X| ≤ m ≤ nd` and `1 ≤ |R| ≤ k` for every core `R`; if every clause has width `k` then
   `m ≤ nd/k`;
3. each core intersects at most `dk` cores of `R_X` (the core itself included). -/
theorem corollary_4_4 {n k d : ℕ} (Φ : CNF n) (hm : 1 ≤ Φ.card)
    (hw : ∀ c ∈ Φ, 1 ≤ width c ∧ width c ≤ k) (hdeg : DegreeBound Φ d)
    (X : Assignment n) (hX : X ∈ solutions Φ) :
    (∀ R₁ ∈ cores Φ X, ∀ R₂ ∈ cores Φ X, R₁ ⊆ R₂ → R₁ = R₂) ∧
    ((cores Φ X).card ≤ Φ.card ∧ Φ.card ≤ n * d ∧
      (∀ R ∈ cores Φ X, 1 ≤ R.card ∧ R.card ≤ k) ∧
      ((∀ c ∈ Φ, width c = k) → (Φ.card : ℝ) ≤ (n : ℝ) * d / k)) ∧
    (∀ R ∈ cores Φ X, ((cores Φ X).filter fun R' => (R' ∩ R).Nonempty).card ≤ d * k) := by sorry

end CNFLearnMQ
