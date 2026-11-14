-- Prove2me | Theorems.Thm_APFPaper5_K3_pqp
-- name    : APFPaper5.K3.pqp
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:23:17.86465+00:00
-- url     : https://prove2.me/theorems/a0d16f40-ee82-43fb-928c-af446a41f998
-- title:
--   The fixed-mark sandwich of a parameterized mark has coefficient u squared
-- statement:
--   For arbitrary real u,v, mul(mul markP(markQ u v))markP=smul(u²)markP. No unit, idempotence or admission hypothesis is required. The coefficient is computed from the explicit supplied array formulas and is not identified with a physical ordered score.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_turn.lean', 'line': 40, 'declaration': 'APFPaper5.K3.pqp', 'sha256': '8a760265b0fcaf3e72921bc878d437508df2077a03d6ae38ed3ef2436a5bb040'}]

import Definitions.Def_APFPaper5_K3_TwoMarkModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.pqp (u v : ℝ) : mul (mul markP (markQ u v)) markP = smul (u * u) markP := by sorry
