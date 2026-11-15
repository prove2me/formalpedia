-- Prove2me | Theorems.Thm_APFPaper5_K3_continuityAtResolution_mono
-- name    : APFPaper5.K3.continuityAtResolution_mono
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:42:24.650148+00:00
-- url     : https://prove2.me/theorems/0dc29c6b-e57b-4677-9f19-3c77eda7187b
-- title:
--   A coarser tolerance preserves the resolution clause
-- statement:
--   If delta ≤ delta-prime and ContinuityAtResolution holds at delta, it holds at delta-prime with the same relation, interval and turn set. The inverse clause is unchanged.
-- source:
--   [{'path': 'source/Theorems/Thm_APFPaper5_K3_continuity_at_resolution.lean', 'sha256': '342fda71dbdd59ee11600cc1eda1484dbcfe2f7230c3e676cfa18274f6b19f3f', 'line': 55, 'declaration': 'APFPaper5.K3.continuityAtResolution_mono'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

import Definitions.Def_APFPaper5_K3_ContinuityAtResolution
import Theorems.Thm_APFPaper5_K3_turn_two_sided_inverse_of_loseNothing
import Theorems.Thm_APFPaper5_K3_exists_noncommuting_of_rangesOver
import Theorems.Thm_APFPaper5_K3_turn_carries_mark
import Theorems.Thm_APFPaper5_K3_twoMark_continuity
import Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u uA

theorem APFPaper5.K3.continuityAtResolution_mono {S : Type u} (rel : S → ℝ) (lo hi delta delta' : ℝ)
    (Adm : Set (S → S)) (hle : delta ≤ delta') (h : ContinuityAtResolution rel lo hi delta Adm) :
    ContinuityAtResolution rel lo hi delta' Adm := by sorry
