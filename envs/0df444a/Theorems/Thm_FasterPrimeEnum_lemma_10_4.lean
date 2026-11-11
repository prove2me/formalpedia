-- Prove2me | Theorems.Thm_FasterPrimeEnum_lemma_10_4
-- name    : FasterPrimeEnum.lemma_10_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:44.170434+00:00
-- url     : https://prove2.me/theorems/292af4d4-6350-465a-984e-2748fef02ba1
-- title:
--   Lemma 10.4 — $\Phi(x,y)\asymp x/\log y$
-- statement:
--   For real $x\ge y\ge2$ let $\Phi(x,y)$ be the number of $y$-rough integers $n\in[1,x]$. Then
--
--   $$
--   \Phi(x,y)\ll\frac{x}{\log y}
--   $$
--
--   for all $x\ge y\ge2$, and if moreover $y<Cx$ for a fixed $C\in(0,1)$, then
--
--   $$
--   \Phi(x,y)\asymp_C\frac{x}{\log y}.
--   $$
--
--   The upper bound controls the number of rough integers, and hence the cost of listing them (Proposition 10.7).
--
--   **Formalization Note** The first bound has one absolute constant; the second has, for each $C\in(0,1)$, a lower and an upper constant depending on $C$ only.
--
--   Differences from the source:
--   - encoding: ≪ and ≍_C → an absolute constant K for (10.1); for each C ∈ (0, 1), constants k, K > 0 depending only on C for (10.2); reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Lemma 10.4, p.96

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsRough

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **Lemma 10.4** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.96.

"For x ⩾ y ⩾ 2 let Φ(x, y) denote the number of y-rough integers n ∈ [1, x]. … For any x ⩾ y ⩾ 2,
(10.1) Φ(x, y) ≪ x/log y. If additionally y < Cx for fixed C ∈ (0, 1) then (10.2)
Φ(x, y) ≍_C x/log y."

**Formalization Note.** `x, y` are real and `Φ(x, y)` is `roughCount x y`. (10.1): one absolute
constant. (10.2): for each `C ∈ (0, 1)`, two constants depending on `C` only, giving the lower and
the upper bound. Both clauses are stated. -/
theorem lemma_10_4 :
    (∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      (roughCount x y : ℝ) ≤ K * x / Real.log y) ∧
    (∀ C : ℝ, 0 < C → C < 1 → ∃ k K : ℝ, 0 < k ∧ 0 < K ∧
      ∀ x y : ℝ, 2 ≤ y → y ≤ x → y < C * x →
        k * x / Real.log y ≤ (roughCount x y : ℝ) ∧
          (roughCount x y : ℝ) ≤ K * x / Real.log y) := by sorry

end FasterPrimeEnum
