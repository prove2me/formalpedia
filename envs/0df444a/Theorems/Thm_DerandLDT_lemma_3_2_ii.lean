-- Prove2me | Theorems.Thm_DerandLDT_lemma_3_2_ii
-- name    : DerandLDT.lemma_3_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:04:46.020521+00:00
-- url     : https://prove2.me/theorems/f334729a-7aba-4ee7-adb6-9e88b055b059
-- title:
--   Lemma 3.2 (second clause) — more than $D^3/12k$ monomials $X^iY^jZ^\ell$ of $(1,1,k)$-degree $\le D$ with $\ell = 0$ or $p \nmid \ell$
-- statement:
--   For all natural numbers $p, k, D$ with $k \ge 1$, $D > 20k$ and $p \ge 2$, the number of monomials $X^i Y^j Z^\ell$ of $(1, 1, k)$-degree at most $D$ (that is, $i + j + k\ell \le D$) whose $Z$-exponent $\ell$ is either zero or not divisible by $p$ is greater than $D^3/12k$:
--   $$
--   \#\{(i, j, \ell) \in \mathbb N^3 : i + j + k\ell \le D,\ \ell = 0 \text{ or } p \nmid \ell\} > \frac{D^3}{12k}.
--   $$
--   This is the second clause of Lemma 3.2. The first clause (all monomials of $(1,1,k)$-degree at most $D$, more than $D^3/6k$) is the published, proved theorem `LineVsPoint.lemma_2_2`, which this mission references. The count is the dimension bound behind the interpolation step (Lemma 6.2) in characteristic $p$: interpolating with monomials whose $Z$-exponent is not a positive multiple of $p$ keeps $\partial_Z Q \neq 0$.
--
--   **Formalization Note** Monomials are their exponent triples; all relevant triples lie in $\{0, \dots, D\}^3$.
--
--   Differences from the source:
--   - encoding: k ∈ ℕ (any) → 1 ≤ k; reason: for k = 0 the monomial set is infinite and D³/12k is undefined
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 3.2 (second clause), p.11

import Mathlib

set_option autoImplicit false

namespace DerandLDT

/-- **Lemma 3.2, second clause** (monomials with `Z`-exponent `0` or prime to `p`).
Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 3.2, p.11: *For all `p, k, D ∈ ℕ` with `D > 20k` and `p ≥ 2`, the number of
monomials `X^i Y^j Z^ℓ` of `(1, 1, k)`-degree at most `D` where `ℓ` is either zero or not
divisible by `p` is greater than `D³/12k`.* The first clause (all monomials, `> D³/6k`) is the
published, proved `LineVsPoint.lemma_2_2`.

**Formalization Note.** A monomial `X^i Y^j Z^ℓ` is its exponent triple `(i, j, ℓ)`; all triples
of `(1, 1, k)`-degree `i + j + kℓ ≤ D` lie in `{0, …, D}³`. The hypothesis `1 ≤ k` is implicit
in the page: for `k = 0` the set is infinite and `D³/12k` is undefined. -/
theorem lemma_3_2_ii :
    ∀ p k D : ℕ, 1 ≤ k → 20 * k < D → 2 ≤ p →
      (D : ℝ) ^ 3 / (12 * k) <
        (((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
          fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + k * m.2.2 ≤ D ∧ (m.2.2 = 0 ∨ ¬ p ∣ m.2.2)).card : ℝ) := by sorry

end DerandLDT
