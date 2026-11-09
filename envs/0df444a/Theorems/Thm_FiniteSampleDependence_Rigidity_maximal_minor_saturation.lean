-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_maximal_minor_saturation
-- name    : FiniteSampleDependence.Rigidity.maximal_minor_saturation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:51:31.092862+00:00
-- url     : https://prove2.me/theorems/6b13ea8f-e138-4e9d-b087-0446d9cc7976
-- title:
--   Proposition 4.3 — $I_n$ is prime and $I_n^2$ is $I_n$-primary
-- statement:
--   Let $2\le n\le m$ and let $I_n\subseteq\mathbb R[X_{i\alpha}]$ be the ideal of maximal ($n\times n$) minors of the generic $n\times m$ matrix. Then
--
--   1. $I_n$ is a prime ideal;
--   2. $I_n^2$ is a primary ideal;
--   3. the radical of $I_n^2$ is $I_n$ (so $I_n^2$ is $I_n$-primary);
--   4. in particular, for all polynomials $a,f$: if $a\notin I_n$ and $af\in I_n^2$, then $f\in I_n^2$.
--
--   This is a standard fact of determinantal algebra (Bruns–Vetter, *Determinantal Rings*, Corollary 9.18). In the rectangular case it removes the pivot factor from $\delta^N H\in I_n^2$.
--
--   Differences from the source:
--   - generalization: the proposition is stated in the paragraph 'Rectangular matrices. For m > n' of Section 4.3 → 2 ≤ n ≤ m (Section 4's standing assumption), so n = m is included; reason: the proposition's own sentence has no condition beyond Section 4's 2 ≤ n ≤ m; the Lean statement specializes to the source's m > n case, and for n = m, I_n = (det X) is principal and prime (Lemma A.1), so the clauses remain true
--   - encoding: n-element column sets S ⊆ [m] → strictly increasing maps Fin n → Fin m; reason: an n-subset listed in increasing order; same set of minors
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Proposition 4.3, PDF p. 14 (printed p. 13); citing Bruns–Vetter 1988, Corollary 9.18

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

namespace FiniteSampleDependence.Rigidity

/-- Proposition 4.3 (Maximal-minor saturation). For `2 ≤ n ≤ m`, the generic maximal-minor ideal
`I_n ⊆ ℝ[X_{iα}]` is prime and `I_n²` is `I_n`-primary (primary with radical `I_n`). In
particular, if `a ∉ I_n` and `a f ∈ I_n²`, then `f ∈ I_n²`. -/
theorem maximal_minor_saturation {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (maxMinorIdeal n m).IsPrime ∧
    (maxMinorIdeal n m ^ 2).IsPrimary ∧
    (maxMinorIdeal n m ^ 2).radical = maxMinorIdeal n m ∧
    ∀ a f : PolyRing n m, a ∉ maxMinorIdeal n m → a * f ∈ maxMinorIdeal n m ^ 2 →
      f ∈ maxMinorIdeal n m ^ 2 := by sorry

end FiniteSampleDependence.Rigidity
