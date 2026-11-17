-- Prove2me | Theorems.Thm_ErrAmpOV_Supplement_theorem_4_1
-- name    : ErrAmpOV.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:19:04.148002+00:00
-- url     : https://prove2.me/theorems/092661f8-3d0c-44e4-8f68-90582a90f271
-- title:
--   Theorem 4.1 — zero-error SORT circuits: error $1/10$ to $2^{-n^{1-\varepsilon-o(1)}}$ at a $\mathrm{poly}(1/\varepsilon)$ factor in size
-- statement:
--   Let $m=m(n)=n^3$, so that $\mathrm{SORT}_{n,m}$ sorts $n$ integers from $[n^3]$, each written in $\lceil\log_2 m\rceil$ bits. Let $f:\mathbb N\to\mathbb R$ be non-decreasing, and suppose that for all sufficiently large $n$,
--   $$\mathrm{SORT}_{n,m}\in\mathrm{ZPSIZE}_{1/10}\bigl[n\log_2 n\cdot f(n)\bigr].$$
--   Then there are constants $C,K>0$ such that for every constant $0<\varepsilon<1$ there is a function $g$ with $g(n)\to0$ such that for all sufficiently large $n$,
--   $$\mathrm{SORT}_{n,m}\in\mathrm{ZPSIZE}_{\delta}\Bigl[C\Bigl(\frac1\varepsilon\Bigr)^{K}\cdot n\log_2 n\cdot f(n)\Bigr],\qquad \delta=2^{-n^{1-\varepsilon-g(n)}} .$$
--
--   Zero-error sorting circuits can thus have their error driven from a constant to nearly $2^{-n}$ at only a constant-factor (for fixed $\varepsilon$) increase in size, whereas independent repetition would cost a factor close to $n$.
--
--   **Formalization Note** $\mathrm{ZPSIZE}_\delta$ for SORT requires, for every valid input and every random string, either the sorted list or $\bot$, and the sorted list with probability at least $1-\delta$. The hypothesis size is exact and its error exactly $1/10$.
--
--   Differences from the source:
--   - reading: poly(1/ε) → ∃ C K > 0, chosen before ε, with size bound C·(1/ε)^K; reason: one polynomial for all ε, as the proof builds it (depth ⌈log(1/ε)/log(3/2)⌉ + 1, factor 8^i/ε); every polynomial is at most C·(1/ε)^K on 1/ε > 1
--   - reading: δ := 2^{−n^{1−ε−o(1)}}, for all sufficiently large n and any constant 0 < ε < 1 → ∃ g : ℕ → ℝ with g → 0, chosen after ε, and ∀ᶠ n the error is at most 2^{−n^{1−ε−g(n)}}; reason: the o(1) is a function of n that may depend on the constant ε; the threshold on n may depend on ε
--   - encoding: x ∈ [m]^n with each element written in log(m) bits; SORT_{n,m}(x) the sorted list → n blocks of Nat.clog 2 m bits (little-endian), circuits constrained only on inputs whose blocks are all < m; output the sorted blocks in the same encoding; reason: Nat.clog 2 m = ⌈log₂ m⌉ is the integer bit width of log(m) bits; the domain is [m]^n, so only valid inputs are constrained
--   - encoding: zero-error circuit: R_{n,m}(x) ∈ {SORT_{n,m}(x), ⊥}; log(n); sizes without O(·) in the hypothesis → ZPSorts: first output wire true means ⊥ with the remaining n·w output wires left free (p.5 pads ⊥ with zeros), success means first wire false followed by the sorted list; log is Real.logb 2; exact hypothesis size; reason: mirrors the published ZPDecides convention (the zero padding of p.5 is a presentation convention, and masking the padding costs n·w + 1 gates, absorbed by the constant C since the hypothesis forces f(n) bounded below); log is in bits (footnote 2)
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 4.1, p.12 (informal version Theorem 1.3, p.2; proof pp.17–19)

import Mathlib
import Definitions.Def_ErrAmpOV_Supplement_ZPSorts

set_option autoImplicit false

open Filter Topology

namespace ErrAmpOV.Supplement

/-- Theorem 4.1 (Error reduction for zero-error probabilistic circuits computing SORT), p.12;
formal version of Theorem 1.3, p.2. Let `m := m(n) = n³` and let `f` be non-decreasing.
Suppose that for all sufficiently large `n`, `SORT_{n,m}` has zero-error probabilistic circuits
of size at most `n·log₂ n·f(n)` with error at most `1/10`. Then there are constants `C, K > 0`
(a polynomial `C·(1/ε)^K`) such that for every constant `0 < ε < 1` there is a function
`g(n) → 0` such that for all sufficiently large `n`, `SORT_{n,m}` has zero-error probabilistic
circuits of size at most `C·(1/ε)^K·n·log₂ n·f(n)` with error at most `2^{−n^{1−ε−g(n)}}`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 4.1, p.12 (proof pp.17–19).

**Formalization Note.**
* "`poly(1/ε)`" is `∃ C K > 0` with the bound `C·(1/ε)^K`, chosen after `f` and before `ε`
  (one polynomial for all `ε`); every polynomial is bounded by such a monomial on `1/ε > 1`.
* "`δ := 2^{−n^{1−ε−o(1)}}`" is `∃ g : ℕ → ℝ`, `g → 0`, chosen after `ε` and before the
  threshold on `n`; the error is `2^{−n^{1−ε−g(n)}}` (`Real.rpow`).
* "For all sufficiently large `n` and any constant `0 < ε < 1`": the threshold may depend on
  `ε` (it is a constant).
* `m = n³` is fixed by `n`; `log` is `Real.logb 2`. The hypothesis size `n·log₂ n·f(n)` is
  exact (no `O`), the error exactly `1/10`. `f : ℕ → ℝ` with `Monotone f`. -/
theorem theorem_4_1 (f : ℕ → ℝ) (hf : Monotone f)
    (h : ∀ᶠ n : ℕ in atTop,
      ZPSorts (1 / 10) ((n : ℝ) * Real.logb 2 n * f n) n (n ^ 3)) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        ZPSorts ((2 : ℝ) ^ (-((n : ℝ) ^ (1 - ε - g n))))
          (C * (1 / ε) ^ K * ((n : ℝ) * Real.logb 2 n * f n)) n (n ^ 3) := by sorry

end ErrAmpOV.Supplement
