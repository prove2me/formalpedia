-- Prove2me | Theorems.Thm_F3SubsetSum_Supplement_theorem_1_11
-- name    : F3SubsetSum.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:31:07.2392+00:00
-- url     : https://prove2.me/theorems/58aed8d6-42d0-4a5a-bbc9-c4d0083656f9
-- title:
--   Theorem 1.11 — classical worst-case $\mathbb F_q^n$-Subset-Sum for $m\ge q^{q^2}(n+1)^{q-1}$
-- statement:
--   Let $q\ge3$ be a prime. The **worst-case $\mathbb F_q^n$-Subset-Sum problem** (Problem 1.9) asks, for arbitrary vectors $h_1,\dots,h_m\in\mathbb F_q^n$, for a nonempty set $S\subseteq[m]$ with $\sum_{i\in S}h_i=0$.
--
--   There are absolute constants $C>0$ and $k\in\mathbb N$ such that for every prime $q\ge3$ there is a deterministic classical algorithm $\mathrm{Alg}$ (a multi-stack Turing machine) with the following property: for all $n,m$ with
--   $$
--   m\ \ge\ q^{q^2}\cdot (n+1)^{q-1},
--   $$
--   1. on every instance $h\in(\mathbb F_q^n)^m$ the algorithm halts within $C(m+1)^k$ steps, and
--   2. on every instance $h$ its output is a nonempty set $S\subseteq[m]$ with $\sum_{i\in S}h_i=0$.
--
--   This replaces the exponent $\Theta(q\log q)$ of $n$ in earlier worst-case algorithms by $q-1$.
--
--   **Formalization Note** Input and output codes are those of Theorem 1.10 (unary entries, indicator bits). The machine depends on $q$; the constants $C,k$ do not.
--
--   Differences from the source:
--   - reading: poly(m) with unsubscripted asymptotics → constants C > 0 and k ∈ ℕ chosen before q, n, m: at most ⌊C(m+1)^k⌋ steps; reason: Notation (p.3): absolute constants unless a subscript names a dependence; the machine depends on the fixed prime q of Problem 1.9
--   - encoding: deterministic classical algorithm that solves the worst-case problem → a Mathlib multi-stack Turing machine computing Alg within the bound on every input, and IsZeroSubsetSumQ h (Alg n m h) for every h ∈ (F_q^n)^m; reason: the paper fixes no machine model; polynomial overheads are absorbed by poly(m)
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 1.11, p.7 (restated p.33; proof §6, pp.33–36)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_Supplement_SubsetSumQ

set_option autoImplicit false

namespace F3SubsetSum.Supplement

/-- **Theorem 1.11** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 1.11,
p.7; restated p.33; proof §6, pp.33–36): "For every m ≥ q^{q²} · (n + 1)^{q−1}, there is a
deterministic classical algorithm that solves the worst-case Problem 1.9 and runs in time poly(m)."

There are absolute constants `C > 0` and `k ∈ ℕ` such that for every prime `q ≥ 3` there is one
deterministic machine `M`, computing a Subset-Sum algorithm `Alg`, such that for all `n, m` with
`m ≥ q^{q²}(n+1)^{q−1}`: on every input `M` halts within `C(m+1)^k` steps with the output of `Alg`,
and for **every** `h ∈ (F_qⁿ)^m` the output `Alg n m h` is a nonempty zero-sum subset.

**Formalization Note** `poly(m)` has no subscript, so `C` and `k` are absolute (Notation, p.3)
and chosen before `q`, `n`, `m`; the machine depends on the fixed prime `q` (Problem 1.9).
`q − 1` is natural-number subtraction with `q ≥ 3`. -/
theorem theorem_1_11 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q →
        ∃ (M : Turing.TM2ComputableAux Bool Bool) (Alg : SubsetSumAlg q),
          ∀ n m : ℕ, q ^ (q ^ 2) * (n + 1) ^ (q - 1) ≤ m →
            SubsetSumComputesWithin M Alg n m ⌊C * ((m : ℝ) + 1) ^ k⌋₊ ∧
            ∀ h : Fin m → Fin n → ZMod q, IsZeroSubsetSumQ h (Alg n m h) := by sorry

end F3SubsetSum.Supplement
