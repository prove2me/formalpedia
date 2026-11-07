-- Prove2me | Theorems.Thm_DiagLinesLDT_proposition_7_2
-- name    : DiagLinesLDT.proposition_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:50.01421+00:00
-- url     : https://prove2.me/theorems/635099fa-bd4f-444a-a131-1b2c722b1d78
-- title:
--   Proposition 7.2 — characteristic-two strategy
-- statement:
--   Let $q=2^r$, and define
--
--   $$A^u_a=\frac1q\sum_{t\in\mathbb F_q}\chi(ta)V(tw(u)),\qquad P^\ell_\lambda=\frac{1}{|S_\ell|}\sum_{v\in S_\ell}\chi(\lambda(v))U_\ell(v),$$
--
--   and $B^\ell_g=\sum_{\lambda:\,h^\ell_\lambda=g}P^\ell_\lambda$, with Bob using the transposed operators. This strategy is projective, satisfies $A^u_a=\sum_{g(u)=a}B^\ell_g$ for $u\in\ell$, is accepted with probability 1 by the self-consistency and axis-parallel tests, and every global measurement $G$ satisfies
--
--   $$\mathbb E_u\sum_a\sum_{g:\,g(u)=a}\langle\Phi|(A^u_a\otimes G_g)|\Phi\rangle\le 1-\frac1{16}\Big(1-\frac1q\Big)^3.$$
--
--   This is the goal theorem for even $q$.
--
--   Differences from the source:
--   - encoding: q = 2^r → finite field F with ringChar F = 2; reason: the same fields
--   - encoding: G with outcomes functions g → G indexed by all functions (Fin 2 → F) → F, zero operators allowed; reason: a measurement with outcomes in a subset of the functions extends by zero
--   - encoding: univariate polynomials f : ℓ → 𝔽_q of degree at most d → functions on ℓ agreeing with a polynomial of natDegree ≤ d along a parametrization; reason: the source writes the answers as functions on ℓ; legality is independent of the parametrization
--   - encoding: projective measurement → MIPRE.IsPVM: Hermitian idempotents summing to 1; reason: mutual orthogonality follows; zero outcomes are allowed as in the source
--   - encoding: ⟨ψ|M ⊗ N|ψ⟩ → its real part; reason: for tensors of Hermitian operators the value is already real
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Proposition 7.2, p.23

import Mathlib
import Definitions.Def_DiagLinesLDT_charTwoStrategy
import Definitions.Def_DiagLinesLDT_reducedAcc

namespace DiagLinesLDT

/-- The characteristic-two strategy: projective, line measurements refine point measurements, accepted
with probability 1 by both retained tests, and bounded away from every global measurement.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Proposition 7.2, p.23.

**Formalization Note** "`q = 2^r`" is `ringChar F = 2`. `G` is indexed by all functions `𝔽_q² → 𝔽_q`. -/
theorem proposition_7_2 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F = 2) :
    (charTwoStrategy F).IsProjective ∧
      (∀ (ℓ : AxisLine F 2) (u : ℓ.1) (a : F),
        pointTwo F u.1 a = ∑ g : LegalAnswer 2 ℓ with g.1 u = a, lineTwo F ℓ g) ∧
      selfAcc (charTwoStrategy F) = 1 ∧
      axisAcc (charTwoStrategy F) = 1 ∧
      ∀ G : ((Fin 2 → F) → F) → Matrix (Fin 3 → F) (Fin 3 → F) ℂ, MIPRE.IsPVM G →
        consistency (charTwoStrategy F) G ≤
          1 - (1 / 16) * (1 - 1 / (Fintype.card F : ℝ)) ^ 3 := by sorry

end DiagLinesLDT
