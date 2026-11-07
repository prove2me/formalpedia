-- Prove2me | Theorems.Thm_DiagLinesLDT_proposition_7_1
-- name    : DiagLinesLDT.proposition_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:57:51.450038+00:00
-- url     : https://prove2.me/theorems/c2437621-b6f3-4aab-ac9c-e8a2559c6d86
-- title:
--   Proposition 7.1 — odd prime-power strategy
-- statement:
--   For every odd prime power $q$, take the label map $w(x,y)=(1,y,y^2;xy^2,-2xy,x)$ and replace every $\omega^t$ in the point and line measurements by $\chi(t)$. The resulting strategy is projective, is accepted with probability 1 by the self-consistency and axis-parallel tests, and every projective global measurement $G$ with function outcomes satisfies
--
--   $$\mathbb E_u\sum_a\sum_{g:\,g(u)=a}\langle\Phi|(A^u_a\otimes G_g)|\Phi\rangle\le 1-\frac1{16}\Big(1-\frac1q\Big)^3.$$
--
--   This is the goal theorem for odd $q$.
--
--   Differences from the source:
--   - encoding: odd prime power q → finite field F with ringChar F ≠ 2; reason: the same fields
--   - encoding: G with outcomes functions g → G indexed by all functions (Fin 2 → F) → F, zero operators allowed; reason: a measurement with outcomes in a subset of the functions extends by zero
--   - encoding: univariate polynomials f : ℓ → 𝔽_q of degree at most d → functions on ℓ agreeing with a polynomial of natDegree ≤ d along a parametrization; reason: the source writes the answers as functions on ℓ; legality is independent of the parametrization
--   - encoding: projective measurement → MIPRE.IsPVM: Hermitian idempotents summing to 1; reason: mutual orthogonality follows; zero outcomes are allowed as in the source
--   - encoding: ⟨ψ|M ⊗ N|ψ⟩ → its real part; reason: for tensors of Hermitian operators the value is already real
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Proposition 7.1, p.22

import Mathlib
import Definitions.Def_DiagLinesLDT_oddStrategy
import Definitions.Def_DiagLinesLDT_reducedAcc

namespace DiagLinesLDT

/-- The odd prime-power strategy: projective, accepted with probability 1 by both retained tests, and
bounded away from every global measurement.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Proposition 7.1, p.22.

**Formalization Note** "Odd prime power" is a finite field of odd characteristic. `G` is indexed by all
functions `𝔽_q² → 𝔽_q`. -/
theorem proposition_7_1 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    (oddStrategy F).IsProjective ∧
      selfAcc (oddStrategy F) = 1 ∧
      axisAcc (oddStrategy F) = 1 ∧
      ∀ G : ((Fin 2 → F) → F) → Matrix (Fin 3 → F) (Fin 3 → F) ℂ, MIPRE.IsPVM G →
        consistency (oddStrategy F) G ≤
          1 - (1 / 16) * (1 - 1 / (Fintype.card F : ℝ)) ^ 3 := by sorry

end DiagLinesLDT
