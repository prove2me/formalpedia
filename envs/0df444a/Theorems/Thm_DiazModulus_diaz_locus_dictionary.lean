-- Prove2me | Theorems.Thm_DiazModulus_diaz_locus_dictionary
-- name    : DiazModulus.diaz_locus_dictionary
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:12:13.90397+00:00
-- url     : https://prove2.me/theorems/5fea543f-9239-417d-b101-37ecf4040dc7
-- title:
--   A candidate is exactly a point of the Diaz locus
-- statement:
--   **The two vocabularies used on this mission name the same set.**
--
--   The conjecture tree is written in terms of `IsCandidate u`: $u \neq 0$, $|u|$ algebraic, $e^{u}$
--   algebraic. The results of the `Diaz.*` family are written in terms of the
--   **Diaz locus**
--
--   $$\mathcal{D} \;=\; \{\, u \in \mathcal{L} \setminus \{0\} \;:\; u\bar{u} \in \bar{\mathbb{Q}} \,\},$$
--
--   whose defining data appear inlined in those statements as the three hypotheses $u \neq 0$,
--   `IsAlgebraic ℚ (Complex.exp u)`, `IsAlgebraic ℚ (u * conj u)`. Nothing on the board records that
--   these are the same condition, so no result stated in one vocabulary can presently be cited by a
--   proof written in the other.
--
--   They are the same condition, and **unconditionally so**: the equivalence needs no transcendence
--   input at all — not Hermite–Lindemann, not six exponentials — and holds for every complex $u$,
--   whether or not a candidate exists.
--
--   **The two clauses.** The second conjunct is the content. Its whole mathematical substance is the
--   chain $|u| \in \bar{\mathbb{Q}} \iff |u|^{2} \in \bar{\mathbb{Q}} \iff u\bar{u} \in \bar{\mathbb{Q}}$,
--   which is already the first conjunct of the published `Diaz.normal_form`; what is added here is only
--   that algebraicity over $\mathbb{Q}$ does not notice the embedding $\mathbb{R} \hookrightarrow
--   \mathbb{C}$, so that the conjecture tree's `IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)` and the locus's
--   `IsAlgebraic ℚ ‖u‖` say the same thing. The proof imports `Diaz.normal_form` and uses exactly that.
--
--   The first conjunct is the other half of the translation, and it is not decoration. Each family
--   carries its own copy of the algebraic numbers — `DiazModulus.Qbar` and `Diaz.Qbar` — declared
--   independently, each as `(algebraicClosure ℚ ℂ).toSubfield`. They are literally the same subfield,
--   the equation holding by `rfl`; but until it is stated, a `DiazModulus` hypothesis cannot be fed to
--   a `Diaz` result quantified over `Diaz.Qbar`, and the instance `Diaz.QbarIsAlgebraic` does not fire on the conjecture tree's base field.
--
--   **What this is, and what it is not.** It is a dictionary, not a decomposition. It makes no part of
--   Diaz's conjecture easier, proves nothing new about candidates, and asserts no existence. Its value
--   is entirely structural: with it, the roughly thirty results of the `Diaz.*` family that are stated
--   over an arbitrary conjugation-stable subfield $K$ with hypotheses `Transcendental K u` and
--   `u * conj u ∈ K` become directly applicable at the mission's own base field, and the conjugation,
--   independence and rigidity statements proved for the locus become statements about candidates.
--
--   The same equivalence in words: Diaz's conjecture asserts $\mathcal{D} = \emptyset$; `IsCandidate`
--   is the predicate whose non-emptiness is the negation of the conjecture. Naming both without saying
--   they agree is the gap this closes.

import Definitions.Def_DiazModulus
import Definitions.Def_Diaz_Instantiation

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_locus_dictionary :
    Qbar = Diaz.Qbar ∧
      ∀ u : ℂ, IsCandidate u ↔
        (u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp u) ∧ IsAlgebraic ℚ (u * conj u)) := by sorry
end DiazModulus
