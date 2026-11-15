-- Prove2me | Theorems.Thm_APFPaper5_K3_not_ranges_of_finitely_many_values
-- name    : APFPaper5.K3.not_ranges_of_finitely_many_values
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:47:51.194518+00:00
-- url     : https://prove2.me/theorems/de8435c4-f5e1-4712-a1e7-da157b063aab
-- title:
--   A finite real range cannot cover a nondegenerate interval
-- statement:
--   For any real-valued map with finite range, proves that RangesOverInterval fails for every choice of interval endpoints. This concerns exact coverage, not finite-tolerance coverage.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 36, 'declaration': 'APFPaper5.K3.not_ranges_of_finitely_many_values'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

import Definitions.Def_APFPaper5_K3_Continuity
import Definitions.Def_APFPaper5_K1_AlignmentCount
import Definitions.Def_APFB02_ToldApart
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod

set_option autoImplicit false

theorem APFPaper5.K3.not_ranges_of_finitely_many_values {S : Type*} (rel : S → ℝ) (lo hi : ℝ)
    (hfin : (Set.range rel).Finite) : ¬ APFPaper5.K3.RangesOverInterval rel lo hi := by sorry
