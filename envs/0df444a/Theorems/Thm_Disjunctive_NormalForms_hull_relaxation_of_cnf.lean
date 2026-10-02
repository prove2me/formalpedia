-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_hull_relaxation_of_cnf
-- name    : Disjunctive.NormalForms.hull_relaxation_of_cnf
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:28:41.511187+00:00
-- url     : https://prove2.me/theorems/c86b2bdd-052a-432c-9b01-f4b35e79e06d
-- title:
--   Lemma 4.5 — the hull-relaxation of a CNF equals its polyhedral part
-- statement:
--   This is Lemma 4.5 of Balas's *Disjunctive Programming* (not found by
--   `statements.jsonl`'s regex extraction; verified directly against the PDF), the opening link of
--   Theorem 4.7's chain.
--
--   For a disjunctive set in CNF, $F_0 = \bigcap_{j \in T} D_j$ with each $D_j$ elementary:
--
--   $$
--   h\text{-}\mathrm{rel}(F_0) = P_0,
--   $$
--
--   where $P_0$ is the polyhedral part (the intersection of the *improper* elementary disjunctions,
--   i.e. the ordinary linear constraints already present). This follows directly from Theorem 4.4:
--   every *proper* elementary conjunct contributes $\mathrm{cl}\,\mathrm{conv}(D_j) = \mathbb{R}^n$
--   to the intersection defining `h-rel`, hence drops out entirely, leaving only the already-polyhedral
--   improper conjuncts. When $F_0$ is the feasible set of a 0-1 program in CNF, this identifies the
--   hull-relaxation with the ordinary LP relaxation.
--
--   **Formalization Note.** `P0Set` and `HRel` are the companion definitions; `hCNF` requires every
--   conjunct to be elementary (a union of halfspaces), matching the lemma's own CNF hypothesis.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 53, Lemma 4.5

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Lemma 4.5 (Balas §4.2, p. 53; not in `statements.jsonl`'s regex extraction): the
hull-relaxation of a disjunctive set in CNF equals its polyhedral part `P₀` — the opening link
of Theorem 4.7's chain. -/
theorem hull_relaxation_of_cnf {n : ℕ} {T : Type*} [Fintype T] (D : T → Set (Fin n → ℝ))
    (hCNF : ∀ j, IsElementaryDisjunction (D j)) :
    HRel D = P0Set D := by sorry

end Disjunctive.NormalForms
