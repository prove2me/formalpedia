-- Prove2me | Theorems.Thm_DiagLinesLDT_theorem_6_2
-- name    : DiagLinesLDT.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:35.48757+00:00
-- url     : https://prove2.me/theorems/7dc3de65-f6dc-4c48-ac39-a5c051b34c1c
-- title:
--   Theorem 6.2 — exact pointwise commutator
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. Fix $u,v\in\mathbb F_q^2$ and set $c(u,v):=\langle w(u),w(v)\rangle$. Then
--
--   $$\Gamma(u,v)=\begin{cases}0,&c(u,v)=0,\\[2pt] \dfrac{2(q-1)}{q},&c(u,v)\ne 0.\end{cases}$$
--
--   So the point measurements commute exactly on a common axis-parallel line, and are a fixed distance from commuting otherwise.
--
--   Differences from the source:
--   - generalization: q an odd prime, ω^t → any finite field of odd characteristic, χ(t), W_χ; reason: at q = p, χ(t) = ω^t and W_χ = W, so this specializes to the printed statement; §7.1 asserts the prime-power form
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Theorem 6.2, p.17 (proof of Proposition 7.1, p.22, for odd prime powers)

import Mathlib
import Definitions.Def_DiagLinesLDT_oddStrategy

namespace DiagLinesLDT

/-- Exact pointwise commutator.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Theorem 6.2, p.17 (extended to odd prime powers in the proof of Proposition 7.1, p.22).

**Formalization Note** Stated for every finite field of odd characteristic; `c(u, v)` is
`symp (w u) (w v)`. The value is real, with `q` cast to `ℝ`. -/
theorem theorem_6_2 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (u v : Fin 2 → F) :
    Gamma (pointOdd F) u v =
      if symp (w u) (w v) = 0 then 0
      else 2 * ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) := by sorry

end DiagLinesLDT
