-- Prove2me | Theorems.Thm_AvgCaseTI_corollary_2_4
-- name    : AvgCaseTI.corollary_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:25.125205+00:00
-- url     : https://prove2.me/theorems/accb50f2-b711-433e-8de1-0b5cfd9bc94d
-- title:
--   Corollary 2.4 — a random pair has at most $q-1$ conjugators to any pair
-- statement:
--   There are absolute constants $c>0$ and $n_0$ such that for every finite field $\mathbb F_q$ and every $n\ge n_0$: if $\mathbf A=(A_1,A_2)$ consists of two independent uniformly random matrices in $\mathrm M(n,q)$, then with probability at least $1-q^{-cn}$, every pair $\mathbf B=(B_1,B_2)\in\mathrm M(n,q)^2$ satisfies
--   $$
--   |\mathrm{Conj}^{\to}(\mathbf A,\mathbf B)|\le q-1,
--   $$
--   where $\mathrm{Conj}^{\to}(\mathbf A,\mathbf B)=\{T\in\mathrm{GL}(n,q):TA_i=B_iT,\ i=1,2\}$.
--
--   **Formalization Note** The bad event is "some $\mathbf B$ has more than $q-1$ conjugators"; its probability is at most $q^{-cn}$.
--
--   Differences from the source:
--
--   - generalization: B an arbitrary fixed pair, probability over A → B quantified inside the event: with probability ≥ 1 − q^{−cn}, every B satisfies the bound; reason: one good event for all B implies the bound for each fixed B
--   - reading: probability 1 − 1/q^{Ω(n)} → ∃ c > 0, n₀ before the field, failure ≤ q^{−cn}; reason: as in Theorem 2.3
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Corollary 2.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_AvgCaseTI_epsGen

set_option autoImplicit false

universe u

namespace AvgCaseTI

/-- **Corollary 2.4 (a random pair has at most `q − 1` conjugators to any pair).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Corollary 2.4, p.15
(PDF p.17): "Let A = (A₁, A₂) ∈ M(n, q)² consist of two independent uniformly random matrices and
B = (B₁, B₂) ∈ M(n, q)² be two arbitrary matrices. Then |Conj→(A, B)| ≤ q − 1 with probability
1 − 1/q^{Ω(n)}."

There are absolute constants `c > 0` and `n₀` such that for every finite field and every `n ≥ n₀`, the
fraction of pairs `A` for which **some** pair `B` has `|Conj→(A, B)| > q − 1` is at most `q^{−cn}`.

**Formalization Note.** The pair `B` is quantified inside the event (one good event serves every
`B`), which implies the printed per-`B` statement. -/
theorem corollary_2_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (K : Type u) [Field K] [Fintype K], ∀ n : ℕ, n₀ ≤ n →
      (Nat.card {A : Fin 2 → Mat K n //
          ∃ B : Fin 2 → Mat K n, ¬ Nat.card (conjCoset A B) ≤ Fintype.card K - 1} : ℝ) /
          Nat.card (Fin 2 → Mat K n) ≤
        (Fintype.card K : ℝ) ^ (-(c * n)) := by sorry

end AvgCaseTI
