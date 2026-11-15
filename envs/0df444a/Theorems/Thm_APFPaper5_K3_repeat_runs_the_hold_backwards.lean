-- Prove2me | Theorems.Thm_APFPaper5_K3_repeat_runs_the_hold_backwards
-- name    : APFPaper5.K3.repeat_runs_the_hold_backwards
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:19:02.747019+00:00
-- url     : https://prove2.me/theorems/da6ee399-c1b8-4b62-9d99-3b02f5171184
-- title:
--   Repeat runs the hold backwards
-- statement:
--   If positive N iterates of D return x, then n forward iterates after n repeats of N-1 iterates return x, for every natural n. This is an iterate identity at a periodic state. It does not prove admission of repeats, reversal of all histories, or an original history-domain binding.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_repeat_runs_backwards.lean', 'sha256': 'ea5ed6cd5659a9114cb453e2ffe952e33d0549a96b4a8bdbc3d2291775ccf028', 'line': 23, 'declaration': 'APFPaper5.K3.repeat_runs_the_hold_backwards'}]

import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.repeat_runs_the_hold_backwards {S : Type*} (D : S → S) (x : S) (N : ℕ) (hN : 0 < N)
    (h : D^[N] x = x) (n : ℕ) : D^[n] ((D^[N - 1])^[n] x) = x := by sorry
