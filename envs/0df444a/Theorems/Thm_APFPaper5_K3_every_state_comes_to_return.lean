-- Prove2me | Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
-- name    : APFPaper5.K3.every_state_comes_to_return
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:07:36.53324+00:00
-- url     : https://prove2.me/theorems/a74c3852-9ac3-43c8-a97f-5cf8d749b4c6
-- title:
--   Every state comes to return
-- statement:
--   For an endomap of a finite type, every starting state eventually reaches a state of positive period. Finite state/process type and global separation are explicit assumptions. Finite capacity and a finite carried family alone are not a proof of those assumptions; no continuum or physical repetition claim follows.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_held_states_and_undo.lean', 'sha256': '09317d508749814bc66fe38131e40d262a4c7555c9b6cb2a91a26b6ff59a135f', 'line': 72, 'declaration': 'APFPaper5.K3.every_state_comes_to_return'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

import Theorems.Thm_APFB01_physicalState_finite
import Theorems.Thm_APFPaper5_K3_undone_hold_returns
import Theorems.Thm_APFB01_undone_hold_returns_every_object

set_option autoImplicit false

universe uX uP

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.every_state_comes_to_return {S : Type*} [Finite S] (D : S → S) (x : S) :
    ∃ k n : ℕ, 0 < n ∧ D^[n] (D^[k] x) = D^[k] x := by sorry
