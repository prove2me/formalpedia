-- Prove2me | Theorems.Thm_Finset_exists_mem_between_of_forall_le
-- name    : Finset.exists_mem_between_of_forall_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T15:10:11.039114+00:00
-- url     : https://prove2.me/theorems/a44208c0-a4c9-4a43-81b6-dd63d93cb250
-- title:
--   A real between two finite families that are pointwise ordered
-- statement:
--   Let $s$ and $r$ be finite sets of indices and let $L,U$ assign a real number to each
--   index. Suppose every member of the first family is below every member of the second:
--
--   $$
--   L(q) \;\le\; U(p) \qquad \text{for all } q\in s,\ p\in r .
--   $$
--
--   Then some single real number sits between them: there is $t\in\mathbb R$ with
--
--   $$
--   L(q)\;\le\; t \quad\text{for all } q\in s,
--   \qquad
--   t \;\le\; U(p) \quad\text{for all } p\in r .
--   $$
--
--   Both families may be empty, and no index set is assumed finite as a type — only the two finite
--   sets matter.
--
--   The pointwise hypothesis is what makes this work: it says the maximum of the lower family does
--   not exceed the minimum of the upper one, and $t$ can be taken to be either. Stated that way the
--   proof is a `Finset.max'`/`Finset.min'` argument with the empty cases handled separately, which
--   is precisely the fiddly part, and the reason it keeps being redone. It is the step that produces
--   a price, a threshold or a multiplier separating a family of lower bounds from a family of upper
--   bounds — from a finite set of incentive constraints, from the two sides of a cut, from the
--   primal and dual values of a finite program. Six accepted proofs in this collection each prove it
--   for themselves.
--
--   **Formalization Note.** `s` and `r` are `Finset ι` for an index type `ι` in `Type`; `L` and `U`
--   are `ι → ℝ` defined on all of `ι`, with only their values on `s` and `r` constrained. The
--   conclusion is an existential over `ℝ`, so the witness is not named.
-- source:
--   Six distinct accepted submissions prove this inline, each for itself. Carved from https://prove2.me/submissions/26d2a55d-e886-4457-bba1-2bfa50047a59, lines 25-35.

import Mathlib

set_option autoImplicit false
open Matrix

theorem Finset.exists_mem_between_of_forall_le {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by sorry
