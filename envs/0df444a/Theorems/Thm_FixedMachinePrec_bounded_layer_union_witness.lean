-- Prove2me | Theorems.Thm_FixedMachinePrec_bounded_layer_union_witness
-- name    : FixedMachinePrec.bounded_layer_union_witness
-- status  : Open
-- author  : @kj
-- created : 2026-11-26T12:23:49.696094+00:00
-- url     : https://prove2.me/theorems/33b2167e-ec12-44b2-8dc8-03d2931ac379
-- title:
--   Failure of union closure for bounded formula size
-- statement:
--   For every positive machine count and leaf budget there is a ranked precedence instance with two sets of that budget whose union cannot be represented within the same budget. Only union is asserted; intersection then follows by duality.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.3, p. 13 and Algorithm 1, p. 5.

import Mathlib
import Definitions.Def_FixedMachinePrec_GenerateFamily

namespace FixedMachinePrec

theorem bounded_layer_union_witness (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : ∃ (N : ℕ) (p : Fin N → Fin N → Prop) (_ : DecidableRel p) (r : Fin N → ℕ), IsStrictOrder' p ∧ IsTopoRank p r ∧ ∃ X ∈ family p r m k, ∃ Y ∈ family p r m k, X ∪ Y ∉ family p r m k := by sorry

end FixedMachinePrec
