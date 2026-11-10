-- Prove2me | Theorems.Thm_EvasivePatterns_corollary_5_2
-- name    : EvasivePatterns.corollary_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:35.21859+00:00
-- url     : https://prove2.me/theorems/ff36e1f1-e181-45b4-a003-691f9aba76b5
-- title:
--   Corollary 5.2 — $\mathrm{cont}(W_{Q_P})=c$, and the normalized $V$ with $Q_P(z)=V(z^c)$
-- statement:
--   Let $P$ be a binary pattern with $c = \gcd \mathrm{Per}(P) < p = \min \mathrm{Per}(P)$. Then
--   $$
--   \mathrm{cont}(W_{Q_P}) = c .
--   $$
--   Moreover, writing $Q_P(z) = V(z^c)$, the normalized polynomial $V \in \mathbb Z[z]$ satisfies $\mathrm{cont}(W_V) = 1$, has rigid support, and obeys the full-norm identity $\|V V^*\|_1 = |\mathrm{supp}\, V|^2$.
--
--   The corollary reduces the general pattern to the case $\gcd = 1$, where Lemma 5.3 applies to $V$.
--
--   Differences from the source:
--   - encoding: the normalized polynomial V with Q_P(z) = V(z^c) → some V ∈ ℤ[z] with Q_P = V ∘ z^c; reason: V is unique since c ≥ 1
--   - encoding: rigid support (every homometric finite set is a translate of S or of its reflection) → Rigid, quantified over nonempty finite integer sets; reason: supp V contains 0 and m/c ≥ 1, so it has at least two points and every set homometric to it is nonempty; no instance changes
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Corollary 5.2, p.8 (PDF p.9), lines 243–245

import Mathlib
import Definitions.Def_EvasivePatterns_periods
import Definitions.Def_EvasivePatterns_signedPeriodPoly
import Definitions.Def_EvasivePatterns_recipWronskian
import Definitions.Def_EvasivePatterns_Rigid
import Definitions.Def_EvasivePatterns_l1Norm

namespace EvasivePatterns

/-- **Corollary 5.2 (Exact content for period polynomials).** If `P` is binary with `c < p`, then
`cont(W_{Q_P}) = c`. Writing `Q_P(z) = V(z^c)`, the normalized polynomial `V` satisfies
`cont(W_V) = 1`, has rigid support and obeys the full-norm identity (6).

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Corollary 5.2, printed p. 8 (PDF p. 9), lines 243–245.

**Formalization Note** `P : List Bool`, `c = gcdPeriods P`, `p = minPeriod P` (`c < p` forces `P`
nonempty). `V` is the integer polynomial with `Q_P = V ∘ z^c` (unique, since `c ≥ 1`). The full-norm
identity (6) for `V` is `‖V V^*‖₁ = |supp V|²`, `V^* = V.reverse`; the support is cast to `ℤ` for
`Rigid`; `cont` is `Polynomial.content`. -/
theorem corollary_5_2 (P : List Bool) (hcp : gcdPeriods P < minPeriod P) :
    (recipWronskian (signedPeriodPoly P)).content = (gcdPeriods P : ℤ) ∧
      ∃ V : Polynomial ℤ, signedPeriodPoly P = V.comp (Polynomial.X ^ gcdPeriods P) ∧
        (recipWronskian V).content = 1 ∧
        Rigid (V.support.image (fun n : ℕ => (n : ℤ))) ∧
        l1Norm (V * V.reverse) = (V.support.card : ℤ) ^ 2 := by sorry

end EvasivePatterns
