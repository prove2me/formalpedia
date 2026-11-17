-- Prove2me | Theorems.Thm_ErrAmpOV_Supplement_theorem_5_1
-- name    : ErrAmpOV.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:19:45.33764+00:00
-- url     : https://prove2.me/theorems/661e0b26-d383-4e0a-8a40-c8a0af4add16
-- title:
--   Theorem 5.1 — bounded-error SORT circuits: error $1/10$ to $n^{-c}$ at size $O(n\log n\cdot f(n)+n\log n(\log\log n)^2)$
-- statement:
--   Let $m=m(n)=n^3$ and let $f:\mathbb N\to\mathbb R$ be non-decreasing. Suppose that for all sufficiently large $n$,
--   $$\mathrm{SORT}_{n,m}\in\mathrm{BPSIZE}_{1/10}\bigl[n\log_2 n\cdot f(n)\bigr],$$
--   i.e. bounded-error probabilistic circuits of that size output the sorted list with probability at least $9/10$. Then for every $c\in\mathbb N$ there is a constant $C>0$ such that for all sufficiently large $n$,
--   $$\mathrm{SORT}_{n,m}\in\mathrm{BPSIZE}_{n^{-c}}\Bigl[C\bigl(n\log_2 n\cdot f(n)+n\log_2 n\cdot(\log_2\log_2 n)^2\bigr)\Bigr].$$
--
--   For bounded-error circuits the error can be made inverse-polynomial at an additive cost of $n\log n(\log\log n)^2$ gates.
--
--   **Formalization Note** $\mathrm{BPSIZE}_\delta$ for SORT has no $\bot$ symbol: the output must equal the sorted list with probability at least $1-\delta$, and is arbitrary otherwise. The hypothesis size is exact; $c=0$ is included.
--
--   Differences from the source:
--   - reading: for all sufficiently large n and every c ∈ N, BPSIZE_δ[O(n log(n)·f(n) + n log(n)·(log(log(n)))²)] for δ := n^{−c} → ∀ c, ∃ C > 0, ∀ᶠ n, size ≤ C·(n log₂ n·f(n) + n log₂ n·(log₂ log₂ n)²) and error ≤ (n^c)⁻¹; reason: the O-constant may depend on c (Theorem 1.4 writes O_c) but not on n; the threshold on n may depend on c
--   - encoding: x ∈ [m]^n with each element written in log(m) bits; SORT_{n,m}(x) the sorted list → n blocks of Nat.clog 2 m bits (little-endian), circuits constrained only on inputs whose blocks are all < m; output the sorted blocks in the same encoding; reason: Nat.clog 2 m = ⌈log₂ m⌉ is the integer bit width of log(m) bits; the domain is [m]^n, so only valid inputs are constrained
--   - encoding: bounded-error circuit outputs SORT_{n,m}(x) with probability ≥ 1 − ε; log(n) → BPSorts: n·w output wires equal to the sorted list on at least (1 − δ)·2^p random strings; log is Real.logb 2; reason: Definition 2.3 specialised to SORT (p.13); log is in bits (footnote 2)
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 5.1, p.19 (informal version Theorem 1.4, p.3; proof pp.20–22)

import Mathlib
import Definitions.Def_ErrAmpOV_Supplement_BPSorts

set_option autoImplicit false

open Filter

namespace ErrAmpOV.Supplement

/-- Theorem 5.1 (Error reduction for bounded-error probabilistic circuits computing SORT),
p.19; formal version of Theorem 1.4, p.3. Let `m := m(n) = n³` and let `f` be non-decreasing.
Suppose that for all sufficiently large `n`, `SORT_{n,m}` has bounded-error probabilistic
circuits of size at most `n·log₂ n·f(n)` with error at most `1/10`. Then for every `c ∈ ℕ`
there is a constant `C > 0` such that for all sufficiently large `n`, `SORT_{n,m}` has
bounded-error probabilistic circuits of size at most
`C·(n·log₂ n·f(n) + n·log₂ n·(log₂ log₂ n)²)` with error at most `n^{−c}`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 5.1, p.19 (proof pp.20–22).

**Formalization Note.**
* The `O(·)` is `∃ C > 0` chosen after `c` and before the threshold on `n` (Theorem 1.4 writes
  `O_c`); "for all sufficiently large `n` and every `c ∈ N`": the threshold may depend on `c`.
* `δ = n^{−c}` is `((n : ℝ) ^ c)⁻¹`; `c = 0` is included ("every `c ∈ N`").
* `m = n³` is fixed by `n`; `log` is `Real.logb 2`. The hypothesis is exact (no `O`), with
  error `1/10`. BPSIZE has no `⊥` and no all-`r` clause. -/
theorem theorem_5_1 (f : ℕ → ℝ) (hf : Monotone f)
    (h : ∀ᶠ n : ℕ in atTop,
      BPSorts (1 / 10) ((n : ℝ) * Real.logb 2 n * f n) n (n ^ 3)) :
    ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      BPSorts (((n : ℝ) ^ c)⁻¹)
        (C * ((n : ℝ) * Real.logb 2 n * f n +
          (n : ℝ) * Real.logb 2 n * (Real.logb 2 (Real.logb 2 n)) ^ 2)) n (n ^ 3) := by sorry

end ErrAmpOV.Supplement
