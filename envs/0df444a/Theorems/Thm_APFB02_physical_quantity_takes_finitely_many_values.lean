-- Prove2me | Theorems.Thm_APFB02_physical_quantity_takes_finitely_many_values
-- name    : APFB02.physical_quantity_takes_finitely_many_values
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:55.11454+00:00
-- url     : https://prove2.me/theorems/c3c396b1-1964-44ad-82e1-570def0d70b2
-- title:
--   ToldApart makes a profile quantity finite-valued
-- statement:
--   Given finite D and ToldApart Cont reads, every supplied real function phi of the continuation predicate Cont x has finite range over x. ToldApart and identification of Cont with the original profile are not proved here.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 91, 'declaration': 'APFB02.physical_quantity_takes_finitely_many_values'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFB02.physical_quantity_takes_finitely_many_values {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → ℝ) :
    (Set.range (fun x : X => phi (Cont x))).Finite := by sorry
