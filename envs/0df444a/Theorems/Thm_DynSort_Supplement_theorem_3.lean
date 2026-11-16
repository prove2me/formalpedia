-- Prove2me | Theorems.Thm_DynSort_Supplement_theorem_3
-- name    : DynSort.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:39:33.227414+00:00
-- url     : https://prove2.me/theorems/d64a18f7-2e23-439a-bf9b-61b60e1f6a82
-- title:
--   Theorem 3 — online sorting with $O(\log\log n)$ competitive ratio and $O(\log\log n)$ amortized recourse
-- statement:
--   Consider the online (insertion-only) sorting problem on an array of $n$ cells: real values arrive one at a time, at most $n$ of them, each must be placed in an empty cell, and previously placed elements may be moved; the **recourse** of an insertion is the number of previously stored elements that change cells. As in the Remark after Theorem 39, the optimal cost $\Omega=\max_j x_j-\min_j x_j$ of the complete insertion sequence is known to the algorithm in advance.
--
--   There are constants $K$ and $N_0$ such that for every $n\ge N_0$ and every $\Omega$ there is a deterministic online algorithm on $n$ cells with the following property. For every insertion-only sequence $\tau$ of at most $n$ insertions whose inserted values have $\mathrm{OPT}=\Omega$:
--
--   1. after every prefix of $\tau$ the arrangement is legal and
--   $$\mathrm{cost}(S)\le K\log\log n\cdot\Omega,$$
--   where $S$ is the sequence of stored values read left to right;
--   2. the total recourse over $\tau$ is at most $K\log\log n\cdot|\tau|$.
--
--   This is an exponential improvement over the $\Theta(\sqrt n)$ competitive ratio achievable without recourse, and it is the point $R=\Theta(\log\log n)$ of the tradeoff of Theorem 39.
--
--   Differences from the source:
--   - encoding: the optimal cost of the complete insertion sequence is known to the algorithm (Remark, p.34) → ∀ Ω before ∃ alg; the guarantee covers every insertion-only τ with opt (insertedValues τ) = Ω; reason: an algorithm chosen after a parameter given in advance is an algorithm that knows that parameter; the sequences with complete optimum Ω are exactly those on which the assumption holds
--   - reading: competitive ratio ρ in online sorting with known optimum → after every prefix of τ the arrangement is legal and its cost is at most ρ·Ω; reason: the paper bounds the cost at any intermediate stage (Claims 40, 41, Lemmas 42, 43) against the known final optimum; this is the guarantee Theorem 4 needs from an online algorithm
--   - encoding: deterministic online algorithm on an array of size n; amortized recourse → the published DynSort.OnlineAlg n (a function of the update history), totalRecourse alg τ ≤ bound·|τ|; reason: the published model of the base mission (§2 definitions); amortized recourse is total recourse divided by the number of updates
--   - encoding: competitive ratio O(log log n) and O(log log n) amortized recourse → ∃ K, ∃ N₀, ∀ n ≥ N₀: cost ≤ K·log(log n)·Ω and total recourse ≤ K·log(log n)·|τ|; reason: the O(·) is one constant chosen before n; N₀ is needed because log log n ≤ 0 for n ≤ 2; log is Real.log
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Theorem 3, §1.1, p.1 (PDF p.3); assumption: Remark after Theorem 39, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_OnlineAlg
import Definitions.Def_DynSort_Supplement_InsertOnly

namespace DynSort.Supplement

open DynSort

/-- **Theorem 3**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §1.1, p.1 (PDF p.3): "There is a deterministic algorithm for the online
sorting problem with competitive ratio O(log log n) and O(log log n) amortized recourse per
insertion." Under the assumption of the Remark on p.34 (PDF p.36), which the paper attaches to
Theorem 39, from which Theorem 3 follows: "the optimal cost of the complete insertion sequence is
known to the algorithm."

**Formalization Note.** One constant `K` and a threshold `N₀`, chosen before `n`
(`log log n ≤ 0` for `n ≤ 2`). For every `n ≥ N₀` and every value `Ω` given in advance (the
known optimum), an online algorithm on exactly `n` cells such that, for every insertion-only
sequence `τ` of at most `n` insertions of arbitrary reals whose complete optimum
`opt (insertedValues τ)` equals `Ω`: after every prefix of `τ` the arrangement is legal and its
cost is at most `K·log log n·Ω`, and the total recourse over `τ` is at most
`K·log log n·|τ|`. `log` is `Real.log`. -/
theorem theorem_3 :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ Ω : ℝ, ∃ alg : OnlineAlg n,
      ∀ τ : List Update, InsertOnly τ → Valid n τ → opt (insertedValues τ) = Ω →
        (∀ k ≤ τ.length, Legal n (τ.take k) (alg (τ.take k)) ∧
          cost (seq (τ.take k) (alg (τ.take k))) ≤ K * Real.log (Real.log n) * Ω) ∧
        (totalRecourse alg τ : ℝ) ≤ K * Real.log (Real.log n) * τ.length := by sorry

end DynSort.Supplement
