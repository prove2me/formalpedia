-- Prove2me | Theorems.Thm_DiagLinesLDT_lemma_5_2
-- name    : DiagLinesLDT.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:47.719625+00:00
-- url     : https://prove2.me/theorems/1c1ba045-bea6-47d8-b7f3-e056ea5b9712
-- title:
--   Lemma 5.2 — line measurements refine point measurements
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. For every axis-parallel line $\ell$, every $u\in\ell$, and every $a\in\mathbb F_q$,
--
--   $$A^u_a=\sum_{g:\,g(u)=a}B^\ell_g,$$
--
--   the sum running over legal answers $g$ of degree at most 2. This identity is the reason the axis-parallel test is passed with probability 1.
--
--   Differences from the source:
--   - generalization: q an odd prime, ω^t → any finite field of odd characteristic, χ(t), W_χ; reason: at q = p, χ(t) = ω^t and W_χ = W, so this specializes to the printed statement; §7.1 asserts the prime-power form
--   - encoding: univariate polynomials f : ℓ → 𝔽_q of degree at most d → functions on ℓ agreeing with a polynomial of natDegree ≤ d along a parametrization; reason: the source writes the answers as functions on ℓ; legality is independent of the parametrization
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Lemma 5.2, p.14 (Proposition 7.1, p.22, for odd prime powers)

import Mathlib
import Definitions.Def_DiagLinesLDT_oddStrategy

namespace DiagLinesLDT

/-- Line measurements refine point measurements.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Lemma 5.2, p.14 (extended to odd prime powers in Proposition 7.1, p.22).

**Formalization Note** Stated for every finite field of odd characteristic; `g` ranges over the legal
answers on `ℓ` of degree at most 2. -/
theorem lemma_5_2 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (ℓ : AxisLine F 2) (u : ℓ.1) (a : F) :
    pointOdd F u.1 a = ∑ g : LegalAnswer 2 ℓ with g.1 u = a, lineOdd F ℓ g := by sorry

end DiagLinesLDT
