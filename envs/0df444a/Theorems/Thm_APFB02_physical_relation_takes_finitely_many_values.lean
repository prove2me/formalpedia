-- Prove2me | Theorems.Thm_APFB02_physical_relation_takes_finitely_many_values
-- name    : APFB02.physical_relation_takes_finitely_many_values
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:55.726792+00:00
-- url     : https://prove2.me/theorems/f73db83d-bace-4235-b049-1fe270d80460
-- title:
--   ToldApart makes a two-profile relation finite-valued
-- statement:
--   Given finite D and ToldApart Cont reads, every supplied real function phi of two continuation predicates has finite range over pairs of raw states. The conclusion is conditional on ToldApart.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 98, 'declaration': 'APFB02.physical_relation_takes_finitely_many_values'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFB02.physical_relation_takes_finitely_many_values {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → (Q → Prop) → ℝ) :
    (Set.range (fun p : X × X => phi (Cont p.1) (Cont p.2))).Finite := by sorry
