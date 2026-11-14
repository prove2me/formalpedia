-- Prove2me | Theorems.Thm_APFPaper5_K3_records_are_cross_data
-- name    : APFPaper5.K3.records_are_cross_data
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:24:40.079977+00:00
-- url     : https://prove2.me/theorems/7b2210b0-5811-4f67-b066-d2fd75629a7f
-- title:
--   The two recombination records equal component costs plus twice their cross terms
-- statement:
--   For every Held2 state, recSum=recA+recB+2 crossRe and recQuarter=recA+recB+2 crossIm. This pair of polynomial identities relates the chosen four records to the two cross terms. It imposes no unit, nonzero, admission or physical-realization hypothesis.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1649'}, {'locator': '1809-1832'}, {'locator': '1957'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_components.lean', 'line': 50, 'declaration': 'APFPaper5.K3.records_are_cross_data', 'sha256': 'f24f1e3f6eb86f0848b62f865fa28c02e83e823ebc1f0921a0b37cce25f85af9'}]

import Definitions.Def_APFPaper5_K3_TwoComponents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.records_are_cross_data (h : Held2) :
    recSum h = recA h + recB h + 2 * crossRe h ∧
      recQuarter h = recA h + recB h + 2 * crossIm h := by sorry
