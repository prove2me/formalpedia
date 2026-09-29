-- Prove2me | Theorems.Thm_Diaz_model_falsifies
-- name    : Diaz.model_falsifies
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:16.52241+00:00
-- url     : https://prove2.me/theorems/027b7427-1575-46fb-8c86-750c5b31f8c3
-- title:
--   The analogue of Diaz's conjecture is false in the model
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $t \in \mathbb{C}$ non-zero with $t\bar t \in K$. Then there are rationals $a, b$ with
--
--   $$a t + b\,\bar t \neq 0, \qquad \mathrm{Exp}_0(a,b) \ \text{algebraic over } \mathbb{Q}, \qquad (a t + b \bar t)\,\overline{(a t + b\bar t)} \in K .$$
--
--   **Why.** Take $(a,b) = (1,0)$: the element is $t \neq 0$, its norm is $t\bar t \in K$ by hypothesis, and $\mathrm{Exp}_0(1,0) = 2$ is algebraic — indeed every value of $\mathrm{Exp}_0$ is, by `Diaz.isAlgebraic_two_rpow`.
--
--   **Role.** This is the statement the whole model exists to make. Diaz's modulus conjecture says that no non-zero $u$ with $e^{u}$ algebraic has algebraic modulus. Its analogue *inside the model* — a non-zero element of the plane whose product with its conjugate lies in the base field and which carries an algebraic formal exponential — is **false**, and this theorem exhibits the witness. So the algebraic configuration a counterexample to Diaz would present is realised by ordinary objects that are not counterexamples. That is what makes the absence of a contradiction, in twenty-two years of attempts on the algebraic side, more than a failure to find one: no argument using only the model's data can succeed, because the model's data are consistent with the conjecture being false.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Exponential.lean#L142-L154

import Mathlib
import Definitions.Def_Diaz_Exponential

open ComplexConjugate
open Diaz

theorem Diaz.model_falsifies {K : Subfield ℂ} {t : ℂ}
    (hρ : t * conj t ∈ K) (ht0 : t ≠ 0) :
    ∃ a b : ℚ, ((a : ℂ) * t + (b : ℂ) * conj t) ≠ 0
      ∧ IsAlgebraic ℚ (Exp0 (a, b))
      ∧ ((a : ℂ) * t + (b : ℂ) * conj t)
          * conj ((a : ℂ) * t + (b : ℂ) * conj t) ∈ K := by sorry
