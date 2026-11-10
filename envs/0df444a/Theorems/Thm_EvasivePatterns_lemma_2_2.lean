-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_2_2
-- name    : EvasivePatterns.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:35.748421+00:00
-- url     : https://prove2.me/theorems/e472509d-c0ae-452c-91c9-8d323930b974
-- title:
--   Lemma 2.2 — alternating enumerator $\sum_n s_nz^n=q_mz^m/Q_P(z)$, and $s_n\neq0\Rightarrow D_P(n)=n$
-- statement:
--   Let $P$ be a binary pattern of length $m$, with signed counts $s_n$, prefix sign $q_m = (-1)^{\mathrm{wt}(P)}$ and signed period polynomial $Q_P$. Then, as formal power series,
--   $$
--   \sum_{n \ge 0} s_n z^n = \frac{q_m z^m}{Q_P(z)},
--   $$
--   and for every $n$, if $s_n \ne 0$ then $D_P(n) = n$.
--
--   The first part turns the question "is $s_n \ne 0$?" into a question about the coefficients of a rational function; the second part is the degree lower bound that converts a nonzero coefficient into full evasiveness at length $n$.
--
--   Differences from the source:
--   - generalization: binary pattern P (the paper's patterns have a smallest period, hence are nonempty) → any P : List Bool, the empty word included; reason: the statement also holds for the empty word, so it specializes to the source's claim for every nonempty P
--   - encoding: formal power series identity with quotient by Q_P(z) → identity in ℚ⟦z⟧ with the integer sequences cast to ℚ and Q_P inverted; reason: Q_P has constant term 1, so it is invertible and the identity is the same over ℤ
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Lemma 2.2, display (7), p.4 (PDF p.5), lines 111–113

import Mathlib
import Definitions.Def_EvasivePatterns_signedPeriodPoly
import Definitions.Def_EvasivePatterns_signedCount
import Definitions.Def_EvasivePatterns_queryComplexity

namespace EvasivePatterns

/-- **Lemma 2.2 (Alternating enumerator; cf. [HHS18]).** For the formal power series of the signed
counts, `Σ_{n≥0} s_n z^n = q_m z^m / Q_P(z)` (7). If `s_n ≠ 0`, then `D_P(n) = n`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Lemma 2.2, display (7), printed p. 4 (PDF p. 5), lines 111–113.

**Formalization Note** `P` is a binary word (`List Bool`); the statement also holds for the empty
word (both sides of (7) equal `1`), which is therefore not excluded; `m = P.length`,
`q_m = prefixSign P m`. Identity (7) is stated in `ℚ⟦z⟧`, where `Q_P` (constant term `1`) is
invertible, with the integer sequences cast to `ℚ`. `D_P(n) = queryComplexity P n`. -/
theorem lemma_2_2 (P : List Bool) :
    PowerSeries.mk (fun n => (signedCount P n : ℚ)) =
        PowerSeries.C (prefixSign P P.length : ℚ) * PowerSeries.X ^ P.length *
          (((signedPeriodPoly P).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)⁻¹ ∧
      ∀ n : ℕ, signedCount P n ≠ 0 → queryComplexity P n = n := by sorry

end EvasivePatterns
