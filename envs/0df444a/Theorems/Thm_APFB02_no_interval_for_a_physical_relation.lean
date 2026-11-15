-- Prove2me | Theorems.Thm_APFB02_no_interval_for_a_physical_relation
-- name    : APFB02.no_interval_for_a_physical_relation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:54.893102+00:00
-- url     : https://prove2.me/theorems/48be8869-a010-470f-9a6f-2ebca85465f6
-- title:
--   A finite ToldApart relation cannot cover an exact interval
-- statement:
--   Given finite readings and ToldApart Cont reads, a real function of two profiles cannot cover a nondegenerate real interval exactly. No failure of finite-resolution continuity or physical continuity in general is proved.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB02_finite_region_has_no_continuum.lean', 'sha256': '3aac9775cd96fb4bf29f44ac501fb2944470dbc1a06e8d32c02a3b675c5d5c09', 'line': 107, 'declaration': 'APFB02.no_interval_for_a_physical_relation'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFB02.no_interval_for_a_physical_relation {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → (Q → Prop) → ℝ) (lo hi : ℝ) :
    ¬ APFPaper5.K3.RangesOverInterval (fun p : X × X => phi (Cont p.1) (Cont p.2)) lo hi := by sorry
