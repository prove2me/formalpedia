-- Prove2me | Theorems.Thm_APFB02_continuity_clause_fails_for_a_physical_relation
-- name    : APFB02.continuity_clause_fails_for_a_physical_relation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:57.029075+00:00
-- url     : https://prove2.me/theorems/56b5df53-aa7f-40be-a1f8-9397b4595c8b
-- title:
--   The strong continuity clause fails for finite ToldApart data
-- statement:
--   Under finite D and ToldApart, the older exact-range Continuity predicate fails for a supplied two-profile relation, for any set of turns. This does not refute the later ContinuityAtResolution predicate.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 114, 'declaration': 'APFB02.continuity_clause_fails_for_a_physical_relation'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFB02.continuity_clause_fails_for_a_physical_relation {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → (Q → Prop) → ℝ) (lo hi : ℝ) (Adm : Set (X × X → X × X)) :
    ¬ APFPaper5.K3.Continuity (fun p : X × X => phi (Cont p.1) (Cont p.2)) lo hi Adm := by sorry
