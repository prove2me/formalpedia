-- Prove2me | Theorems.Thm_APFB02_overlap_of_two_states_takes_finitely_many_values
-- name    : APFB02.overlap_of_two_states_takes_finitely_many_values
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:54.925989+00:00
-- url     : https://prove2.me/theorems/14e89507-6834-4326-aca6-4343d1e01933
-- title:
--   Finite Boolean overlap takes finitely many values
-- statement:
--   For a finite indexed reading family, the sum of products of the two states' ±1 readings has finite range. This is a property of the defined count relation.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 78, 'declaration': 'APFB02.overlap_of_two_states_takes_finitely_many_values'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFB02.overlap_of_two_states_takes_finitely_many_values {X D : Type*} [Fintype D]
    (reads : D → X → Bool) :
    (Set.range (fun p : X × X =>
      overlapOn Finset.univ (fun d => reads d p.1) (fun d => reads d p.2))).Finite := by sorry
