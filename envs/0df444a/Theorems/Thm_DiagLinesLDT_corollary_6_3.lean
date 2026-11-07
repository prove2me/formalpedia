-- Prove2me | Theorems.Thm_DiagLinesLDT_corollary_6_3
-- name    : DiagLinesLDT.corollary_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:41.158589+00:00
-- url     : https://prove2.me/theorems/9d1a833d-1247-43fa-8abb-6d09f3d94346
-- title:
--   Corollary 6.3 — exact averaged commutator
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. For independent uniformly random $u,v\in\mathbb F_q^2$,
--
--   $$\mathbb E_{u,v}\Gamma(u,v)=2\Big(1-\frac1q\Big)^3.$$
--
--   Combined with Theorem 6.4, this is the source of the constant in the goal theorem.
--
--   Differences from the source:
--   - generalization: q an odd prime, ω^t → any finite field of odd characteristic, χ(t), W_χ; reason: at q = p, χ(t) = ω^t and W_χ = W, so this specializes to the printed statement; §7.1 asserts the prime-power form
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Corollary 6.3, p.18 (proof of Proposition 7.1, p.22, for odd prime powers)

import Mathlib
import Definitions.Def_DiagLinesLDT_oddStrategy
import Definitions.Def_DiagLinesLDT_reducedAcc

namespace DiagLinesLDT

/-- Exact averaged commutator.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Corollary 6.3, p.18 (extended to odd prime powers in the proof of Proposition 7.1, p.22).

**Formalization Note** Stated for every finite field of odd characteristic; `u, v` are independent, and
`u = v` is included. -/
theorem corollary_6_3 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    uniformAvg (fun u : Fin 2 → F => uniformAvg fun v : Fin 2 → F => Gamma (pointOdd F) u v) =
      2 * (1 - 1 / (Fintype.card F : ℝ)) ^ 3 := by sorry

end DiagLinesLDT
