-- Prove2me | Theorems.Thm_APFB02_relation_of_two_states_takes_finitely_many_values
-- name    : APFB02.relation_of_two_states_takes_finitely_many_values
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:57.872202+00:00
-- url     : https://prove2.me/theorems/2328b530-97b5-4fc3-a0b0-1d9d66ffdeec
-- title:
--   Finite readings give a finite range to a two-state relation
-- statement:
--   For finite D, if a supplied real relation is invariant under equality of all Boolean readings in each argument, its range on X × X is finite. The invariance hypothesis is explicit and does not follow merely from finite D.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 48, 'declaration': 'APFB02.relation_of_two_states_takes_finitely_many_values'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

import Definitions.Def_APFPaper5_K3_Continuity
import Definitions.Def_APFPaper5_K1_AlignmentCount
import Definitions.Def_APFB02_ToldApart
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod

set_option autoImplicit false



namespace APFB02
end APFB02
open APFB02
open APFPaper5.K1

theorem APFB02.relation_of_two_states_takes_finitely_many_values {X D : Type*} [Finite D]
    (reads : D → X → Bool) (rel : X → X → ℝ)
    (hrel : ∀ x x' y y' : X, (∀ d, reads d x = reads d x') → (∀ d, reads d y = reads d y') →
      rel x y = rel x' y') :
    (Set.range (fun p : X × X => rel p.1 p.2)).Finite := by sorry
