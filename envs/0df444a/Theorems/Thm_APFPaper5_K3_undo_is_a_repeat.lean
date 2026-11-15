-- Prove2me | Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
-- name    : APFPaper5.K3.undo_is_a_repeat
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:11:58.702818+00:00
-- url     : https://prove2.me/theorems/c5ae48a3-4e9c-4aef-b9a7-a52f7a868053
-- title:
--   Undo is a repeat
-- statement:
--   Supporting result: undo is a repeat. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Positive-period states admit repeat undo; an endomap is injective on its periodic states. Finite domains imply eventual periodicity, and invariant predicates persist. A finite separating Boolean family implies a finite domain; a finite process domain gives a quotient instance. Finite state/process type and global separation are explicit assumptions. Finite capacity and a finite carried family alone are not a proof of those assumptions; no continuum or physical repetition claim follows.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_held_states_and_undo.lean', 'sha256': '09317d508749814bc66fe38131e40d262a4c7555c9b6cb2a91a26b6ff59a135f', 'line': 39, 'declaration': 'APFPaper5.K3.undo_is_a_repeat'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

import Theorems.Thm_APFB01_physicalState_finite
import Theorems.Thm_APFPaper5_K3_undone_hold_returns
import Theorems.Thm_APFB01_undone_hold_returns_every_object

set_option autoImplicit false

universe uX uP

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.undo_is_a_repeat {S : Type*} (D : S → S) (x : S) (n : ℕ) (hn : 0 < n)
    (h : D^[n] x = x) : D^[n - 1] (D x) = x := by sorry
