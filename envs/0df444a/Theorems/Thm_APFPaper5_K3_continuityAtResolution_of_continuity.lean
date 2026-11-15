-- Prove2me | Theorems.Thm_APFPaper5_K3_continuityAtResolution_of_continuity
-- name    : APFPaper5.K3.continuityAtResolution_of_continuity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:42:21.207016+00:00
-- url     : https://prove2.me/theorems/4847bb6c-d094-46f1-8f21-8a0e4695a4c3
-- title:
--   The strong clause implies each nonnegative-resolution clause
-- statement:
--   For delta ≥ 0, the older exact Continuity predicate implies ContinuityAtResolution for unchanged relation, interval and Adm. This is an implication between named predicates.
-- source:
--   [{'path': 'source/Theorems/Thm_APFPaper5_K3_continuity_at_resolution.lean', 'sha256': '342fda71dbdd59ee11600cc1eda1484dbcfe2f7230c3e676cfa18274f6b19f3f', 'line': 49, 'declaration': 'APFPaper5.K3.continuityAtResolution_of_continuity'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFPaper5.K3.continuityAtResolution_of_continuity {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ)
    (Adm : Set (S → S)) (hd : 0 ≤ delta) (h : Continuity rel lo hi Adm) :
    ContinuityAtResolution rel lo hi delta Adm := by sorry
