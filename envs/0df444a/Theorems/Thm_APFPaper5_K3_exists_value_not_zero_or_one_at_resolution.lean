-- Prove2me | Theorems.Thm_APFPaper5_K3_exists_value_not_zero_or_one_at_resolution
-- name    : APFPaper5.K3.exists_value_not_zero_or_one_at_resolution
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:42:20.543637+00:00
-- url     : https://prove2.me/theorems/cb1a579b-9e5e-492e-a6df-791d2a86f9f8
-- title:
--   Fine interval coverage forces a value other than zero and one
-- statement:
--   If RangesAtResolution holds and 4delta < hi-lo, some state's relation value is neither zero nor one. This does not assert that its value lies strictly between zero and one.
-- source:
--   [{'path': 'source/Theorems/Thm_APFPaper5_K3_continuity_at_resolution.lean', 'sha256': '342fda71dbdd59ee11600cc1eda1484dbcfe2f7230c3e676cfa18274f6b19f3f', 'line': 84, 'declaration': 'APFPaper5.K3.exists_value_not_zero_or_one_at_resolution'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFPaper5.K3.exists_value_not_zero_or_one_at_resolution {S : Type u} (rel : S → ℝ)
    (lo hi delta : ℝ) (hd : 4 * delta < hi - lo) (h : RangesAtResolution rel lo hi delta) :
    ∃ s : S, rel s ≠ 0 ∧ rel s ≠ 1 := by sorry
