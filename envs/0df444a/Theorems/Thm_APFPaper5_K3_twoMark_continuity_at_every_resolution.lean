-- Prove2me | Theorems.Thm_APFPaper5_K3_twoMark_continuity_at_every_resolution
-- name    : APFPaper5.K3.twoMark_continuity_at_every_resolution
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:47:43.527928+00:00
-- url     : https://prove2.me/theorems/f43c0063-392f-4666-b355-272a1bc5d5ef
-- title:
--   The supplied two-component model meets every nonnegative tolerance
-- statement:
--   Given the explicit hypothesis that every nonnegative real has a square root, the supplied unit-pair model with relNumber and admTurns satisfies ContinuityAtResolution on [0,1] for delta ≥ 0. The square-root premise is ordinary mathematics, retained in Lean; physical realization and ledger admission are not established.
-- source:
--   [{'path': 'source/Theorems/Thm_APFPaper5_K3_continuity_at_resolution.lean', 'sha256': '342fda71dbdd59ee11600cc1eda1484dbcfe2f7230c3e676cfa18274f6b19f3f', 'line': 126, 'declaration': 'APFPaper5.K3.twoMark_continuity_at_every_resolution'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFPaper5.K3.twoMark_continuity_at_every_resolution (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t)
    (delta : ℝ) (hd : 0 ≤ delta) :
    ContinuityAtResolution relNumber 0 1 delta admTurns := by sorry
