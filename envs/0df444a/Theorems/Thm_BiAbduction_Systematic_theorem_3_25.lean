-- Prove2me | Theorems.Thm_BiAbduction_Systematic_theorem_3_25
-- name    : BiAbduction.Systematic.theorem_3_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:05.567189+00:00
-- url     : https://prove2.me/theorems/28f449db-d9f4-4989-b83d-551e8afa74ea
-- title:
--   Theorem 3.25 — the ≾-minimal solution of Δ ∗ D ⊨ H is a computable disjunction of symbolic heaps
-- statement:
--   Consider the abduction question (5) of the Points-to Instantiation,
--   $$\Delta*D\models H,$$
--   where $\Delta=\Pi\wedge L_1\mapsto R_1*\dots*L_n\mapsto R_n$ is a quantifier-free symbolic heap and $H=\exists\vec X.\Pi'\wedge\Sigma'$ a symbolic heap. There is an algorithm which, given $\Delta$ and $H$, returns a disjunction $D$ of symbolic heaps that is the minimal solution w.r.t. $\precsim$: $\Delta*D\models H$, and $D\precsim M$ for every predicate $M$ (arbitrary set of states) with $\Delta*M\models H$.
--
--   This is the paper's main result on the systematic algorithm: the best abductive solution, which semantically is $\min(\Delta\mathbin{-\!\!*}H)$, can be expressed in the language of symbolic heaps and computed.
--
--   **Formalization Note** "Effectively computed with an algorithm" is `Computable₂ f` for a single function `f : LHS → SH → Disj`, with Mathlib's standard `Primcodable` encodings of lists, pairs, sums, booleans and naturals. The competitors $M$ range over all predicates, not only over disjunctions. No bound-variable convention is assumed: renaming the bound variables of $H$ does not change its denotation, so the statement covers the page's case.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 34, Theorem 3.25

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax

namespace BiAbduction.Systematic

/-- Theorem 3.25 (p. 34), Minimal Solution Algorithm. The minimal solution w.r.t. `≾` of the
abduction question `Δ ∗ D ⊨ H` (5) is expressible as a disjunction `D` of symbolic heaps, which is
computed from `(Δ, H)` by an algorithm. -/
theorem theorem_3_25 :
    ∃ f : LHS → SH → Disj, Computable₂ f ∧
      ∀ (Δ : LHS) (H : SH), IsLeastSolution (lhsDen Δ) (shDen H) (disjDen (f Δ H)) := by sorry

end BiAbduction.Systematic
