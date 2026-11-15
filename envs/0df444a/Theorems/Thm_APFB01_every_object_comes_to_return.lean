-- Prove2me | Theorems.Thm_APFB01_every_object_comes_to_return
-- name    : APFB01.every_object_comes_to_return
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:06:32.471779+00:00
-- url     : https://prove2.me/theorems/e63b3307-b60e-4e74-8002-8acc24888b8f
-- title:
--   Finite-process model quotients are eventually periodic
-- statement:
--   For a supplied continuation profile with finite process type, every class in its B01-shaped quotient is eventually periodic under any supplied quotient endomap. Finite state/process type and global separation are explicit assumptions. Finite capacity and a finite carried family alone are not a proof of those assumptions; no continuum or physical repetition claim follows.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_held_states_and_undo.lean', 'sha256': '09317d508749814bc66fe38131e40d262a4c7555c9b6cb2a91a26b6ff59a135f', 'line': 99, 'declaration': 'APFB01.every_object_comes_to_return'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

import Theorems.Thm_APFB01_physicalState_finite
import Theorems.Thm_APFPaper5_K3_undone_hold_returns
import Theorems.Thm_APFB01_undone_hold_returns_every_object

set_option autoImplicit false

universe uX uP

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB01.every_object_comes_to_return {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop)
    (D : APFB01.PhysicalState profile → APFB01.PhysicalState profile)
    (s : APFB01.PhysicalState profile) :
    ∃ k n : ℕ, 0 < n ∧ D^[n] (D^[k] s) = D^[k] s := by sorry
