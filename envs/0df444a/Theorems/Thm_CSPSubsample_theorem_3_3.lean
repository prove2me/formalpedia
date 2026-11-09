-- Prove2me | Theorems.Thm_CSPSubsample_theorem_3_3
-- name    : CSPSubsample.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:46.999202+00:00
-- url     : https://prove2.me/theorems/9e36c061-789d-4654-ba20-0cb45d084f4f
-- title:
--   Theorem 3.3 (Subsampling) — a uniform sample of $N=c\,k^{12}\varepsilon^{-6}\log^2(qk^2/\varepsilon)$ variables gives $|\mathbb E[\mathrm{OPT}(U)]-\mathrm{OPT}|\le O(\varepsilon)$
-- statement:
--   There exist absolute constants $c>0$ and $C>0$ such that the following holds for all $n,k,q\in\mathbb N$, every $\varepsilon>0$ and every $k$-CSP instance on $n$ variables with alphabet $[q]$. Let
--   $$
--   N=\Big\lceil c\,\frac{k^{12}}{\varepsilon^6}\log^2\!\big(qk^2/\varepsilon\big)\Big\rceil,
--   $$
--   and let $U$ be a set of $N$ variables sampled uniformly without replacement from $[n]$. If
--   $$
--   n\ge c^2\,\frac{k^{24}}{\varepsilon^{13}}\log^4\!\big(qk^2/\varepsilon\big),
--   $$
--   then
--   $$
--   \big|\mathbb E[\mathrm{OPT}(U)]-\mathrm{OPT}\big|\le C\varepsilon .
--   $$
--   The sample size is polynomial in the arity $k$ and in $1/\varepsilon$ and polylogarithmic in $q$; the previous subsampling theorem (Barak, Hardt, Holenstein, Steurer, SODA 2011) needed a sample exponential in $k$. The theorem is the missing ingredient in the proof that $\mathrm{AM}(\mathrm{poly})=\mathrm{AM}$ (Aaronson, Impagliazzo, Moshkovitz, CCC 2014) and yields a one-sided satisfiability tester with $\tilde O(k^{12}\log^2q/\varepsilon^7)$ samples.
--
--   Differences from the source:
--   - reading: N = c k¹²/ε⁶ log²(qk²/ε) (a real number) → N = ⌈c k¹²/ε⁶ log²(qk²/ε)⌉, a natural number; reason: a sample size is an integer; the ceiling is the least size at least the printed quantity
--   - reading: O(ε) → C·ε with an absolute constant C > 0 chosen, like c, before n, k, q, ε and the instance; reason: the paper's constants are absolute ("positive absolute constant c"; the proof's O(kε) is rescaled by ε/k)
--   - reading: log → the natural logarithm Real.log; reason: a change of base rescales c·log² and c²·log⁴ consistently (c ↦ c/ln²b), so the statement does not depend on the base
--   - encoding: E over U sampled uniformly without replacement → the average over all N-subsets of [n]; reason: same law
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Theorem 3.3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_val
import Definitions.Def_CSPSubsample_valOn
import Definitions.Def_CSPSubsample_avgSub

set_option autoImplicit false

namespace CSPSubsample

/-- **Theorem 3.3 (Subsampling)** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.7 = PDF p.9).
There is a positive absolute constant `c` such that, letting `N = c k¹²/ε⁶ log²(qk²/ε)`, `U` a
set of `N` variables sampled uniformly without replacement from `[n]`, and assuming
`n ≥ c² k²⁴/ε¹³ log⁴(qk²/ε)`, `|E[OPT(U)] − OPT| ≤ O(ε)`.

**Formalization Note** `c` and the `O(ε)` constant `C` are absolute: both are chosen before
`n, k, q, ε` and the instance. `N` is the natural number `⌈c k¹²ε⁻⁶ log²(qk²/ε)⌉₊`; `log` is
`Real.log`. `E` over `U` is the average over all `N`-subsets (`avgSub`); `OPT(U)` maximizes
`val_U` (normalized by `|U|^k`, constraints inside `U`). No hypothesis beyond the printed one:
for `ε ≤ 1` it implies `N ≤ n`, and for `ε > 1` the bound is trivial when `C ≥ 1`. -/
theorem theorem_3_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n k q : ℕ) (ε : ℝ), 0 < ε → ∀ I : Instance n k q,
      c ^ 2 * (k : ℝ) ^ 24 / ε ^ 13 * Real.log (q * (k : ℝ) ^ 2 / ε) ^ 4 ≤ n →
      |avgSub n ⌈c * (k : ℝ) ^ 12 / ε ^ 6 * Real.log (q * (k : ℝ) ^ 2 / ε) ^ 2⌉₊ (OPTOn I) -
          OPT I| ≤ C * ε := by sorry

end CSPSubsample
