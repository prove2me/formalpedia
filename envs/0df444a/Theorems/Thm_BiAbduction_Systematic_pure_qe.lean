-- Prove2me | Theorems.Thm_BiAbduction_Systematic_pure_qe
-- name    : BiAbduction.Systematic.pure_qe
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:20.854079+00:00
-- url     : https://prove2.me/theorems/4f317aed-5af1-41c6-9f40-b20970380817
-- title:
--   §3.4.4 — quantifier removal for pure formulae: ∃X.Π is equivalent to a computable Π′ without X
-- statement:
--   There is an algorithm that, given a variable $X$ and a pure formula $\Pi$ (a conjunction of equalities and disequalities between variables and constants), returns a pure formula $\Pi'$ in which $X$ does not occur such that
--   $$\exists X.\,\Pi\ \equiv\ \Pi'.$$
--
--   This quantifier removal is what allows subtraction of symbolic heaps with quantifiers to be expressed again as a disjunction of symbolic heaps.
--
--   **Formalization Note** Pure formulae are read with an unconstrained heap ($\Pi\wedge\mathsf{true}$). The equivalence uses that there are infinitely many values (here all naturals). "Algorithm" is `Computable₂` for Mathlib's standard encodings.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 33, §3.4.4, Quantifier-removal for pure formulae

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax

namespace BiAbduction.Systematic

/-- §3.4.4, quantifier removal for pure formulae (p. 33): for every variable `X` and pure formula
`Π`, the formula `∃X. Π` is equivalent to a pure formula `Π'` in which `X` does not occur, and
`Π'` is computed from `(X, Π)` by an algorithm. -/
theorem pure_qe :
    ∃ qe : ℕ → List PureAtom → List PureAtom, Computable₂ qe ∧
      ∀ (X : ℕ) (pi : List PureAtom),
        X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi) := by sorry

end BiAbduction.Systematic
