-- Prove2me | Theorems.Thm_DetANN_lemma_3_3
-- name    : DetANN.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:46.394608+00:00
-- url     : https://prove2.me/theorems/b84f0bcb-ff28-4c67-81c0-3ebf578b649e
-- title:
--   Lemma 3.3, p.7 — deterministic $(1+\delta)$-ANN in $\mathbb R^m$ with space $n(C/\delta)^{O(m)}\mathrm{polylog}(n/\delta)$ and query time $O(m^2\log^2(n/\delta))$
-- statement:
--   Let $Y\subseteq\mathbb R^m$ be nonempty with at most $n$ points, $m\ge1$, and $\delta\in(0,1/2)$. There is a deterministic data structure that returns a $(1+\delta)$-approximate nearest neighbor in $Y$ for every query $q\in\mathbb R^m$. For an absolute constant $C>1$ its space is $n(C/\delta)^{O(m)}\mathrm{polylog}(n/\delta)$, its preprocessing time is $\mathrm{poly}(n,m)(C/\delta)^{O(m)}\mathrm{polylog}(n/\delta)$, and its query time is $O(m^2\log^2(n/\delta))$.
--
--   Precisely: there are deterministic programs and constants $C>1$, $K,C'\in\mathbb N$, fixed before the instance, such that for every list $Y_0,\dots,Y_{N-1}$ of $N\ge1$ distinct points of $\mathbb R^m$ and every $\delta\in(0,1/2)$:
--
--   1. preprocessing halts within $C'(N+m)^K(C/\delta)^{Km}\log^K(N/\delta)$ steps;
--   2. preprocessing stores to at most $C'N(C/\delta)^{Km}\log^K(N/\delta)$ cells;
--   3. every query halts within $C'm^2\log^2(N/\delta)$ steps with a $(1+\delta)$-approximate nearest neighbor.
--
--   It is the low-dimensional primitive (approximate Voronoi diagrams of Har-Peled) used on every superblock projection.
--
--   **Formalization Note** Machine and data-structure semantics as in `DetANN.IsDetANNStructure`.
--
--   Differences from the source:
--   - reading: a deterministic data structure (no machine named) → deterministic programs of PNormReg.Machine without coin and rpow, with the layouts of IsDetANNStructure; space = distinct cells stored to by preprocessing; reason: the same machine reading as the goal
--   - reading: for each Y, δ there is a data structure; O(m), poly, polylog → one pair of programs and constants C > 1, K, C′ for all instances, δ an input; explicit powers with K; reason: the uniform reading is the stronger one; explicit constants are the meaning of the O-notation
--   - encoding: Y ⊆ ℝ^m nonempty with at most n points → an injective list of N ≥ 1 points, bounds stated with n = N; reason: every bound increases with n, so n = |Y| is the strongest choice and implies the bound for every n ≥ |Y|
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Lemma 3.3, p.7 (PDF p.7); proof in Appendix A, p.19

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure

namespace DetANN

/-- **Lemma 3.3** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), p.7).
For a nonempty `Y ⊆ ℝ^m` with at most `n` points (`m ≥ 1`) and `δ ∈ (0, 1/2)` there is a deterministic
data structure returning a `(1 + δ)`-approximate nearest neighbor for every query in `ℝ^m`, with
space `n(C/δ)^{O(m)} polylog(n/δ)`, preprocessing time `poly(n, m)(C/δ)^{O(m)} polylog(n/δ)` and query
time `O(m² log²(n/δ))`, for an absolute constant `C > 1`.

**Formalization Note.** Same machine and data-structure semantics as `DetANN.theorem_1_1`, with input
parameter `δ`. One pair of programs and the constants `C > 1`, `K`, `C'` come before the instance.
`Y` is an injective list of `N ≥ 1` points and the bounds are stated with `n := N`; since every bound
increases with `n`, this is equivalent to "at most `n` points". `poly(n, m) ≤ C'(n + m)^K`,
`(C/δ)^{O(m)} ≤ (C/δ)^{K m}` (`Real.rpow`), `polylog(n/δ) ≤ (log(n/δ))^K`; `log(N/δ) > log 2 > 0` on the
domain. -/
theorem lemma_3_3 :
    ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
      ∃ C : ℝ, 1 < C ∧ ∃ K C' : ℕ, ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
          ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
            IsDetANNStructure Pre Qry Y δ (1 + δ)
              ((C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
              ((C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
              ((C' : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2) := by sorry

end DetANN
