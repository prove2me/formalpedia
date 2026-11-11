-- Prove2me | Theorems.Thm_FasterPrimeEnum_proposition_2_9
-- name    : FasterPrimeEnum.proposition_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:49.986798+00:00
-- url     : https://prove2.me/theorems/521dac8b-8f2f-4523-a8ef-412f6c1351a7
-- title:
--   Proposition 2.9 — $\Psi_d=2H_d+F$
-- statement:
--   For $d\in D$ let $\psi_d(n)$ be the number of ideals of $\mathbb Z[\sqrt d]$ of norm $n$ for odd $n\ge1$, and $\psi_d(n)=0$ for even $n$, and let $\Psi_d(x)=\sum_{n\ge1}\psi_d(n)x^n$. Then
--
--   $$
--   \Psi_d(x)=2H_d(x)+F(x).
--   $$
--
--   This identity over $\mathbb Z$ is the bridge from the arithmetic of $\mathbb Z[\sqrt d]$ to the series $H_d$, and the step from which Theorem 2.6 is deduced.
--
--   **Formalization Note** Stated coefficientwise for every $n\ge0$; at $n=0$ both sides vanish.
--
--   Differences from the source:
--   - encoding: an identity of power series in Z⟦x⟧ → for every n ≥ 0, idealCount d n = 2·H d n + F n in ℤ; reason: equality of series is equality of all coefficients
--   - encoding: ideals of Z[√d] of norm n → ideals I of ℤ√d with Nat.card (ℤ√d ⧸ I) = n; reason: the norm of a nonzero ideal is its index; the zero ideal has infinite index and is never counted at odd n
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Proposition 2.9, p.16; p.15 (ψ_d, Ψ_d)

import Mathlib
import Definitions.Def_FasterPrimeEnum_restrictedProd
import Definitions.Def_FasterPrimeEnum_H
import Definitions.Def_FasterPrimeEnum_idealCount

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **Proposition 2.9** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.16.

"For d ∈ D we have Ψ_d(x) = 2H_d(x) + F(x)."

Here `Ψ_d(x) := Σ_{n⩾1} ψ_d(n) x^n`, where `ψ_d(n)` is the number of ideals of `Z[√d]` of norm `n`
for odd `n` and `0` for even `n` (p.15).

**Formalization Note.** Stated coefficientwise, as an identity in `ℤ` for every `n`; at `n = 0`
both sides are `0` (`Ψ_d` has no constant term). -/
theorem proposition_2_9 :
    ∀ d ∈ D, ∀ n : ℕ, (idealCount d n : ℤ) = 2 * H d n + F n := by sorry

end FasterPrimeEnum
