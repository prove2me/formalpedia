-- Prove2me | Theorems.Thm_DiagLinesLDT_lemma_4_8
-- name    : DiagLinesLDT.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:20.479207+00:00
-- url     : https://prove2.me/theorems/9c5c261b-1abe-40a5-b341-7247cbd07cee
-- title:
--   Lemma 4.8 — isotropy of the line-label space
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. For every axis-parallel line $\ell$, the subspace $S_\ell$ is isotropic: $\langle v,v'\rangle=0$ for all $v,v'\in S_\ell$. Consequently,
--
--   $$W_\chi(v)W_\chi(v')=W_\chi(v+v')\quad\text{for all }v,v'\in S_\ell.$$
--
--   So $v\mapsto W_\chi(v)$ is a representation of $S_\ell$, whose joint measurement produces the line answers.
--
--   Differences from the source:
--   - generalization: q an odd prime, ω^t → any finite field of odd characteristic, χ(t), W_χ; reason: at q = p, χ(t) = ω^t and W_χ = W, so this specializes to the printed statement; §7.1 asserts the prime-power form
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Lemma 4.8, p.11 (Proposition 7.1, p.22, for odd prime powers)

import Mathlib
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

/-- Isotropy of the line-label space.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Lemma 4.8, p.11 (extended to odd prime powers in Proposition 7.1, p.22).

**Formalization Note** Stated for every finite field of odd characteristic, with `W = W_χ`. -/
theorem lemma_4_8 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (ℓ : AxisLine F 2) :
    (∀ v ∈ lineSpan ℓ, ∀ v' ∈ lineSpan ℓ, symp v v' = 0) ∧
      (∀ v ∈ lineSpan ℓ, ∀ v' ∈ lineSpan ℓ, Wop v * Wop v' = Wop (v + v')) := by sorry

end DiagLinesLDT
