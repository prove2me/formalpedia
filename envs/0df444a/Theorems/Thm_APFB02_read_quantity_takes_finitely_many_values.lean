-- Prove2me | Theorems.Thm_APFB02_read_quantity_takes_finitely_many_values
-- name    : APFB02.read_quantity_takes_finitely_many_values
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:55.765922+00:00
-- url     : https://prove2.me/theorems/f76555a8-6100-4c42-8533-1b50f060809b
-- title:
--   A quantity determined by finite readings has finite range
-- statement:
--   For finite D and a real quantity q invariant whenever all supplied Boolean readings agree, proves q has finite range. The readout-determination premise hq remains explicit.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 68, 'declaration': 'APFB02.read_quantity_takes_finitely_many_values'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFB02.read_quantity_takes_finitely_many_values {X D : Type*} [Finite D]
    (reads : D → X → Bool) (q : X → ℝ)
    (hq : ∀ x x' : X, (∀ d, reads d x = reads d x') → q x = q x') :
    (Set.range q).Finite := by sorry
