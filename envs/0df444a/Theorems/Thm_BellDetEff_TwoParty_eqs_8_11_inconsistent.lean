-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_eqs_8_11_inconsistent
-- name    : BellDetEff.TwoParty.eqs_8_11_inconsistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:19.932838+00:00
-- url     : https://prove2.me/theorems/3dd616bd-9caa-4f26-aab7-6c321e6ba564
-- title:
--   Eqs. (8)–(11) — the congruences a_i + b_j ≡ x_i y_j (mod P) have no common solution for a prime P
-- statement:
--   Let $P$ be a prime and let $x_1,x_2,y_1,y_2$ be integers with $1\le x_1\ne x_2\le P$ and $1\le y_1\ne y_2\le P$. Then there are no residues $a_1,a_2,b_1,b_2\in\mathbb Z/P\mathbb Z$ such that
--   $$a_1+b_1\equiv x_1y_1,\qquad a_1+b_2\equiv x_1y_2,\qquad a_2+b_1\equiv x_2y_1,\qquad a_2+b_2\equiv x_2y_2 \pmod P.$$
--
--   This is Case 2 of the proof of Theorem 2: if A answers on two different inputs and B answers on two different inputs, then at least one of the four corresponding coefficients of the Bell expression is $-P^4$.
--
--   **Formalization Note** The residues are elements of `ZMod P`, and $x_i,y_j$ are natural numbers cast into `ZMod P`.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, pp. 2–3, proof of Theorem 2, Case 2, eqs. (8)–(11)

import Mathlib

namespace BellDetEff.TwoParty

/-- Eqs. (8)–(11), proof of Theorem 2 (Cao–Peng, arXiv:1607.04350v1, pp. 2–3): for a prime `P`
and `1 ≤ x₁ ≠ x₂ ≤ P`, `1 ≤ y₁ ≠ y₂ ≤ P`, no `a₁, a₂, b₁, b₂` satisfy the four congruences
`a_i + b_j ≡ x_i y_j (mod P)`. -/
theorem eqs_8_11_inconsistent (P : ℕ) [Fact P.Prime] (x₁ x₂ y₁ y₂ : ℕ)
    (hx₁ : 1 ≤ x₁) (hx₁P : x₁ ≤ P) (hx₂ : 1 ≤ x₂) (hx₂P : x₂ ≤ P)
    (hy₁ : 1 ≤ y₁) (hy₁P : y₁ ≤ P) (hy₂ : 1 ≤ y₂) (hy₂P : y₂ ≤ P)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (a₁ a₂ b₁ b₂ : ZMod P) :
    ¬ (a₁ + b₁ = (x₁ : ZMod P) * y₁ ∧ a₁ + b₂ = (x₁ : ZMod P) * y₂ ∧
        a₂ + b₁ = (x₂ : ZMod P) * y₁ ∧ a₂ + b₂ = (x₂ : ZMod P) * y₂) := by sorry

end BellDetEff.TwoParty
