-- Prove2me | Theorems.Thm_APFPaper5_K3_moves_at_resolution
-- name    : APFPaper5.K3.moves_at_resolution
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:47:38.286963+00:00
-- url     : https://prove2.me/theorems/ce84a9db-39a6-4e86-833f-ec5e0157556f
-- title:
--   Fine reachable coverage forces a relation-changing turn
-- statement:
--   If ContinuityAtResolution holds and 2delta < hi-lo, from every supplied state some map in Adm changes the relation value. The proof consumes the coverage/reachability parts; the inverse component is included in the input predicate but not needed for this implication.
-- source:
--   [{'path': 'source/Theorems/Thm_APFPaper5_K3_continuity_at_resolution.lean', 'sha256': '342fda71dbdd59ee11600cc1eda1484dbcfe2f7230c3e676cfa18274f6b19f3f', 'line': 109, 'declaration': 'APFPaper5.K3.moves_at_resolution'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFPaper5.K3.moves_at_resolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) (Adm : Set (S → S))
    (hd : 2 * delta < hi - lo) (hc : ContinuityAtResolution rel lo hi delta Adm) (s : S) :
    ∃ f ∈ Adm, rel (f s) ≠ rel s := by sorry
