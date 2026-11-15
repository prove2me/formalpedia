-- Prove2me | Theorems.Thm_APFPaper5_K3_exists_noncommuting_at_resolution
-- name    : APFPaper5.K3.exists_noncommuting_at_resolution
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:42:23.55144+00:00
-- url     : https://prove2.me/theorems/db5ff114-f175-44bc-a66d-3aade13fd837
-- title:
--   Fine relation coverage forces a noncommuting algebraic pair
-- statement:
--   For a supplied real algebra, idempotents p(s),q(s), p(s) nonzero, and compression identity p(s)q(s)p(s)=rel(s) • p(s), interval coverage with 4delta < hi-lo yields a state whose pair does not commute. The algebraic representation, idempotence, nonzero p, compression law and coverage are explicit hypotheses; no original physical representation is constructed.
-- source:
--   [{'path': 'source/Theorems/Thm_APFPaper5_K3_continuity_at_resolution.lean', 'sha256': '342fda71dbdd59ee11600cc1eda1484dbcfe2f7230c3e676cfa18274f6b19f3f', 'line': 96, 'declaration': 'APFPaper5.K3.exists_noncommuting_at_resolution'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}]

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

theorem APFPaper5.K3.exists_noncommuting_at_resolution {S : Type u} {A : Type uA} [Ring A] [Algebra ℝ A]
    (p q : S → A) (rel : S → ℝ) (lo hi delta : ℝ)
    (hp : ∀ s : S, p s * p s = p s) (hq : ∀ s : S, q s * q s = q s) (hp0 : ∀ s : S, p s ≠ 0)
    (hrel : ∀ s : S, p s * q s * p s = rel s • p s)
    (hd : 4 * delta < hi - lo) (h : RangesAtResolution rel lo hi delta) :
    ∃ s : S, p s * q s ≠ q s * p s := by sorry
