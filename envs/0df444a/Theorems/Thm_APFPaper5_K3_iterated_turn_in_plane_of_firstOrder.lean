-- Prove2me | Theorems.Thm_APFPaper5_K3_iterated_turn_in_plane_of_firstOrder
-- name    : APFPaper5.K3.iterated_turn_in_plane_of_firstOrder
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:45:43.161503+00:00
-- url     : https://prove2.me/theorems/6965b048-4990-4b8e-9f90-67285678f391
-- title:
--   A linear map satisfying a cyclic recurrence keeps every iterate in the initial two-vector span
-- statement:
--   On a supplied real module, let T be additive and real-homogeneous. Assume FirstOrder T z, meaning that T(T z) is a real linear combination of z and T z. For every natural n, T iterated n times at z is a real linear combination of those same two vectors. This proves span containment, not their linear independence, an exact dimension, or equivalence to source first-jet completeness. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1649'}, {'locator': '3037-3056'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_exchange_needs_room.lean', 'line': 96, 'declaration': 'APFPaper5.K3.iterated_turn_in_plane_of_firstOrder', 'sha256': '44eed3c43002bff09d87533d14394b2960c86d480a48e7b7c6853ea607f65077'}]

import Definitions.Def_APFPaper5_K3_ThreeDirections
import Definitions.Def_APFPaper5_K3_FirstOrder
import Theorems.Thm_APFPaper5_K3_no_turn_exchanges
import Theorems.Thm_APFPaper5_K3_slant_pqp
import Theorems.Thm_APFPaper5_K1_one_number_cannot_carry_value_and_rate
import Theorems.Thm_APFPaper5_K1_iterated_turn_in_plane
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.iterated_turn_in_plane_of_firstOrder {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V → V) (hTadd : ∀ a b : V, T (a + b) = T a + T b)
    (hTsmul : ∀ (r : ℝ) (a : V), T (r • a) = r • T a) (z : V) (h : FirstOrder T z) :
    ∀ n : ℕ, ∃ a b : ℝ, T^[n] z = a • z + b • T z := by sorry
