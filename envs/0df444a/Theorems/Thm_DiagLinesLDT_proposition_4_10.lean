-- Prove2me | Theorems.Thm_DiagLinesLDT_proposition_4_10
-- name    : DiagLinesLDT.proposition_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:57:37.671087+00:00
-- url     : https://prove2.me/theorems/5e12bd05-4ec3-4fe2-a6ef-b103cd1b0c13
-- title:
--   Proposition 4.10 — line measurements are projective
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. For every axis-parallel line $\ell$, the family $\{P^\ell_\lambda\}_{\lambda\in S_\ell^*}$ is a projective measurement on $\mathcal H$: for all $\lambda,\mu\in S_\ell^*$,
--
--   $$(P^\ell_\lambda)^\dagger=P^\ell_\lambda,\qquad P^\ell_\lambda P^\ell_\mu=\delta_{\lambda,\mu}P^\ell_\lambda,\qquad\sum_{\lambda\in S_\ell^*}P^\ell_\lambda=I.$$
--
--   Consequently, grouping these projections according to $h^\ell_\lambda=g$ makes $\{B^\ell_g\}_g$, over the legal answers $g:\ell\to\mathbb F_q$ of degree at most 2, a projective measurement.
--
--   The last clause contains the fact that every induced answer $h^\ell_\lambda$ has degree at most 2.
--
--   Differences from the source:
--   - generalization: q an odd prime, ω^t → any finite field of odd characteristic, χ(t), W_χ; reason: at q = p, χ(t) = ω^t and W_χ = W, so this specializes to the printed statement; §7.1 asserts the prime-power form
--   - encoding: univariate polynomials f : ℓ → 𝔽_q of degree at most d → functions on ℓ agreeing with a polynomial of natDegree ≤ d along a parametrization; reason: the source writes the answers as functions on ℓ; legality is independent of the parametrization
--   - encoding: projective measurement → MIPRE.IsPVM: Hermitian idempotents summing to 1; reason: mutual orthogonality follows; zero outcomes are allowed as in the source
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Proposition 4.10, p.12 (Proposition 7.1, p.22, for odd prime powers)

import Mathlib
import Definitions.Def_DiagLinesLDT_oddStrategy

namespace DiagLinesLDT

open scoped Classical in
/-- Line measurements are projective.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Proposition 4.10, p.12 (extended to odd prime powers in Proposition 7.1, p.22).

**Formalization Note** Stated for every finite field of odd characteristic; at `q` prime it is the
printed statement. "Consequently" is the last clause, on the legal answers of degree at most 2. -/
theorem proposition_4_10 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (ℓ : AxisLine F 2) :
    (∀ lam, (projOdd F ℓ lam).conjTranspose = projOdd F ℓ lam) ∧
      (∀ lam mu, projOdd F ℓ lam * projOdd F ℓ mu = if lam = mu then projOdd F ℓ lam else 0) ∧
      (∑ lam, projOdd F ℓ lam = 1) ∧
      MIPRE.IsPVM (lineOdd F ℓ) := by sorry

end DiagLinesLDT
