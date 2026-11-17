-- Prove2me | Theorems.Thm_F3SubsetSum_Supplement_theorem_1_10
-- name    : F3SubsetSum.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:30:32.14467+00:00
-- url     : https://prove2.me/theorems/7399d0b5-31fd-44ee-bb8c-2f2ae0df50ea
-- title:
--   Theorem 1.10 — classical average-case $\mathbb F_q^n$-Subset-Sum for $m\ge q^{q^2}n^{1+\lfloor(q+3)/4\rfloor}$
-- statement:
--   Let $q\ge3$ be a prime and let $h_1,\dots,h_m\in\mathbb F_q^n$ be independent and uniformly random. The **average-case $\mathbb F_q^n$-Subset-Sum problem** (Problem 1.9) asks for a nonempty set $S\subseteq[m]$ with $\sum_{i\in S}h_i=0$.
--
--   There are absolute constants $C,c>0$ and $k\in\mathbb N$ such that for every prime $q\ge3$ there is a deterministic classical algorithm $\mathrm{Alg}$ (a multi-stack Turing machine) with the following property: for all $n,m$ with
--   $$
--   m\ \ge\ q^{q^2}\cdot n^{1+\lfloor (q+3)/4\rfloor},
--   $$
--   1. on every instance $h\in(\mathbb F_q^n)^m$ the algorithm halts within $C(m+1)^k$ steps, and
--   2. $\Pr_h\big[\mathrm{Alg}(h)\text{ is a nonempty zero-sum subset}\big]\ \ge\ 1-2^{-cn}.$
--
--   This is the classical average-case algorithm of the paper; for $q\ge5$ it lowers the exponent of $n$ in the required number of vectors from $2\lfloor(q+3)/4\rfloor+1$ (prior work) to $\lfloor(q+3)/4\rfloor+1$.
--
--   **Formalization Note** The instance is read in the code $1^n0\,1^m0$ followed by every entry $v\in\{0,\dots,q-1\}$ as $1^v0$; the output is the $m$ indicator bits of $S$. The machine depends on $q$; the constants $C,c,k$ do not (the paper's unsubscripted $\Omega$ and $\mathrm{poly}$ hide absolute constants).
--
--   Differences from the source:
--   - reading: 1 − 2^{−Ω(n)} and poly(m) with unsubscripted asymptotics → constants c, C > 0 and k ∈ ℕ chosen before q, n, m: success ≥ 1 − 2^{−cn}, at most ⌊C(m+1)^k⌋ steps; reason: Notation (p.3): asymptotic notation hides absolute constants unless a subscript names a dependence; the machine itself depends on the fixed prime q of Problem 1.9
--   - encoding: deterministic classical algorithm running in time poly(m) → a Mathlib multi-stack Turing machine (TM2ComputableAux Bool Bool) that on the unary code of every instance halts within the bound with the indicator code of Alg n m h (HMBinPacking.OutputsWithin); reason: the paper fixes no machine model; Turing machines and RAMs differ by polynomial factors, absorbed by poly(m); input length is polynomial in m since n, q ≤ m under the threshold
--   - encoding: probability over h_1, …, h_m independent and uniform in F_q^n → number of h ∈ (F_q^n)^m on which the output is a solution, divided by q^{nm}; reason: uniform distribution on a finite set; failure is reported by a non-solution output
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 1.10, p.7 (restated p.29; proof §5, pp.29–32)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_Supplement_SubsetSumQ

set_option autoImplicit false

namespace F3SubsetSum.Supplement

/-- **Theorem 1.10** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 1.10,
p.7; restated p.29; proof §5, pp.29–32): "For every m ≥ q^{q²} · n^{1+⌊(q+3)/4⌋}, there is a
deterministic classical algorithm that solves the average-case Problem 1.9 with probability at
least 1 − 2^{−Ω(n)} and runs in time poly(m)."

There are absolute constants `C, c > 0` and `k ∈ ℕ` such that for every prime `q ≥ 3` there is one
deterministic machine `M`, computing a Subset-Sum algorithm `Alg`, such that for all `n, m` with
`m ≥ q^{q²} n^{1+⌊(q+3)/4⌋}`: on every input `M` halts within `C(m+1)^k` steps with the output of
`Alg`, and for `h` uniform in `(F_qⁿ)^m` the output `Alg n m h` is a nonempty zero-sum subset with
probability at least `1 − 2^{−cn}`.

**Formalization Note** The asymptotic notation of the paper hides absolute constants unless a
subscript names a dependence (Notation, p.3); `Ω(n)` and `poly(m)` have no subscript, so `c`, `C`,
`k` are chosen before `q`, `n`, `m`. The machine depends on the fixed prime `q` (Problem 1.9).
`⌊(q+3)/4⌋` is natural-number division. The `+1` in `(m+1)^k` only covers `m = 0`. -/
theorem theorem_1_10 :
    ∃ (C c : ℝ) (k : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q →
        ∃ (M : Turing.TM2ComputableAux Bool Bool) (Alg : SubsetSumAlg q),
          ∀ n m : ℕ, q ^ (q ^ 2) * n ^ (1 + (q + 3) / 4) ≤ m →
            SubsetSumComputesWithin M Alg n m ⌊C * ((m : ℝ) + 1) ^ k⌋₊ ∧
            1 - (2 : ℝ) ^ (-(c * n)) ≤ avgSuccessProb Alg n m := by sorry

end F3SubsetSum.Supplement
