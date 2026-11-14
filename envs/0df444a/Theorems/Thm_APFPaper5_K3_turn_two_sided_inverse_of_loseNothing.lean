-- Prove2me | Theorems.Thm_APFPaper5_K3_turn_two_sided_inverse_of_loseNothing
-- name    : APFPaper5.K3.turn_two_sided_inverse_of_loseNothing
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:37:31.405442+00:00
-- url     : https://prove2.me/theorems/f3d34efc-b873-4939-afae-b7211fa948e1
-- title:
--   Admitted left inverses for every admitted map yield admitted two-sided inverses
-- statement:
--   Let Adm be a set of self-maps of any type S satisfying TurnsLoseNothing: each admitted map has an admitted left inverse. Then every f in Adm has a g in Adm with g(f s)=s and f(g s)=s for every s. Applying the same left-inverse property to g supplies the second inverse identity. No topological or group-closure premise is used. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_continuity_consequences.lean', 'line': 28, 'declaration': 'APFPaper5.K3.turn_two_sided_inverse_of_loseNothing', 'sha256': '4fe8ac46703b4872830c2a80c2c5f4b7092d9fc3d9375ceb62e57001b7a01493'}]

import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFPaper1_RecordBook_pair_number_zero_or_one_of_commute
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u uA
variable {S : Type u}

theorem APFPaper5.K3.turn_two_sided_inverse_of_loseNothing (Adm : Set (S → S)) (h : TurnsLoseNothing Adm)
    (f : S → S) (hf : f ∈ Adm) :
    ∃ g ∈ Adm, (∀ s : S, g (f s) = s) ∧ (∀ s : S, f (g s) = s) := by sorry
