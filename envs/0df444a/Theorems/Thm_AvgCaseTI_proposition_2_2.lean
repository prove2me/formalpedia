-- Prove2me | Theorems.Thm_AvgCaseTI_proposition_2_2
-- name    : AvgCaseTI.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:05.295033+00:00
-- url     : https://prove2.me/theorems/4806634d-cd19-4ead-bef9-9f3da058b044
-- title:
--   Proposition 2.2 — $c(q)^q\ge e^{-23/9}$
-- statement:
--   For every $q\ge2$, with $c(q)=\prod_{i\ge1}(1-q^{-i})$,
--   $$
--   c(q)^q\ \ge\ \exp\Bigl(-1-\frac{3}{2q}-\frac{29}{9q^2}\Bigr)\ \ge\ e^{-23/9},\qquad\text{and}\qquad \frac{q\,c(q)^q}{q-1}\ \ge\ e^{-23/9}.
--   $$
--
--   These uniform lower bounds turn the limiting probabilities of Theorems 6.3 and 6.11 into absolute constants, which is what makes the success fraction of Theorem 1.1 of order $1/q$.
--
--   **Formalization Note** $q$ ranges over all reals $q\ge2$ and $c(q)^q$ is a real power.
--
--   Differences from the source:
--
--   - generalization: q a prime power ≥ 2 → every real q ≥ 2; reason: the proof (p.14) uses only q ≥ 2; prime powers are a special case
--   - encoding: c(q) = lim c_n(q) (an infinite product) → `cInf q`, the infimum of the decreasing positive partial products → same value; reason: Lean convention
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_AvgCaseTI_cn

set_option autoImplicit false

namespace AvgCaseTI

/-- **Proposition 2.2 (lower bounds on `c(q)^q`).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.2, p.14
(PDF p.16): for every `q ≥ 2`,
`c(q)^q ≥ exp(−1 − 3/(2q) − 29/(9q²)) ≥ e^{−23/9}` and `q·c(q)^q/(q − 1) ≥ e^{−23/9}`.

**Formalization Note.** Stated for every real `q ≥ 2` (the paper's `q` is a prime power; its proof
uses only `q ≥ 2`). `c(q)` is `cInf q`, and `c(q)^q` is a real power. -/
theorem proposition_2_2 (q : ℝ) (hq : 2 ≤ q) :
    Real.exp (-1 - 3 / (2 * q) - 29 / (9 * q ^ 2)) ≤ cInf q ^ q ∧
    Real.exp (-(23 / 9)) ≤ Real.exp (-1 - 3 / (2 * q) - 29 / (9 * q ^ 2)) ∧
    Real.exp (-(23 / 9)) ≤ q * cInf q ^ q / (q - 1) := by sorry

end AvgCaseTI
