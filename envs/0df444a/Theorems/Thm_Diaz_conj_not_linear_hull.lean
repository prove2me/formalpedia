-- Prove2me | Theorems.Thm_Diaz_conj_not_linear_hull
-- name    : Diaz.conj_not_linear_hull
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:41.080693+00:00
-- url     : https://prove2.me/theorems/1f4be2e6-bdb5-4090-bf35-4dfc8c120a44
-- title:
--   Conjugation on the hull is not $K$-linear when $K$ contains a non-real number
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield, $u \in \mathbb{C}$, and write $K(u) = \operatorname{hull}(K,u)$. Let $a \in \mathbb{C}$ satisfy $\bar a \neq a$. Then
--
--   $$\neg\ \Big(\forall\, z \in K(u), \quad \overline{a z} = a\,\bar z\Big).$$
--
--   That is, complex conjugation restricted to the hull does **not** commute with multiplication by $a$; in particular it is not a $K$-linear map once the base field $K$ contains a single non-real element.
--
--   **Why.** A counterexample is $z = 1$, which lies in every subfield: the displayed identity at $z=1$ reads $\bar a = a$, contradicting the hypothesis. Note that the statement quantified over the hull is *stronger* than the same statement quantified over all of $\mathbb{C}$, because its negation asserts the existence of a witness inside the smaller set — and the witness $1$ is available there.
--
--   **Role.** This is a **corrected form of an assertion made in an earlier draft of the accompanying note**, which described the involution on the hull as a $\bar{\mathbb{Q}}$-algebra involution — that is, as fixing every algebraic number. It does not. The involution is a *ring* involution and nothing stronger, and since the intended base is the field of algebraic numbers (which contains $i$), the failure of linearity is not a corner case but the generic situation. The theorem is the error stated as a refuted proposition, which is how the formalisation records it.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Closure.lean#L105-L113

import Mathlib
import Definitions.Def_Diaz_Closure

open ComplexConjugate
open Diaz
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem Diaz.conj_not_linear_hull {a : ℂ} (hne : conj a ≠ a) :
    ¬ (∀ z ∈ hull K u, conj (a * z) = a * conj z) := by sorry
