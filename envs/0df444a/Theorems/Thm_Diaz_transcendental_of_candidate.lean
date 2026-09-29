-- Prove2me | Theorems.Thm_Diaz_transcendental_of_candidate
-- name    : Diaz.transcendental_of_candidate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:20.589835+00:00
-- url     : https://prove2.me/theorems/3cae2e48-64f1-4be8-be0d-69719a233f94
-- title:
--   A counterexample to Diaz's conjecture is transcendental over $\mathbb{Q}$
-- statement:
--   Let $u \in \mathbb{C}$ with $u \neq 0$ and suppose $e^{u}$ is algebraic over $\mathbb{Q}$. Then
--
--   $$u \ \text{ is transcendental over } \mathbb{Q}.$$
--
--   ("Transcendental over $\mathbb{Q}$" is by definition the negation of "algebraic over $\mathbb{Q}$": $u$ is a root of no non-zero rational polynomial.)
--
--   **Why.** This is the contrapositive of the Hermite–Lindemann theorem. If $u$ were algebraic and non-zero, Hermite–Lindemann would make $e^{u}$ transcendental, contradicting the hypothesis that it is algebraic.
--
--   **What it rests on.** The single-exponent Hermite–Lindemann theorem — *for every non-zero algebraic $a$, $e^{a}$ is transcendental* — is a theorem of Hermite (1873) and Lindemann (1882), but it is **not present in the platform's Mathlib**: only the analytic half of the Lindemann–Weierstrass development is there. It is a published node of this library, `DiazModulus.hermite_lindemann_holds`, still open, and this theorem reduces to it. The passage between the two forms is the classical contraposition just described and carries no arithmetic content.
--
--   **Role.** In the source project this is the single point of contact between the algebraic development and the imported transcendence input: every other theorem in the project that depends on Hermite–Lindemann depends on it *through this one statement*. Publishing it as a node with an explicit reduction is what turns a global assumption into a visible edge of the dependency graph.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Closure.lean#L144-L148

import Mathlib

open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem Diaz.transcendental_of_candidate (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) : Transcendental ℚ u := by sorry
