-- Prove2me | Theorems.Thm_APFPaper1_Foundation_feasible_ofSource
-- name    : APFPaper1.Foundation.feasible_ofSource
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:18:33.542274+00:00
-- url     : https://prove2.me/theorems/c6d51bc3-303f-4221-9f88-c561071e90ac
-- title:
--   Feasibility of the source ledger is source feasibility
-- statement:
--   For a designated protocol $p_0$ and fixed source protocol/support data, let $L$ be the ledger constructed by the source adapter. For every finite distinction family $S$,
--
--   $$\operatorname{Feasible}(L,S)\ \Longleftrightarrow\ \operatorname{familyFeasible}(S).$$
--
--   Both sides assert that one protocol serves every member from its own maintained sufficient support. This bridge needs no zero-bill condition and establishes neither affordability nor attainment.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Theorems.Thm_APFPaper1_Foundation_feasible_ofSource; source SHA256 7222df7a5baf8216bd3f49e6afe7c8499d47668dee59507d19d7cac68da35192. See the source header for original v9.27 line references and the November 11 testedness ruling.

import Definitions.Def_APFPaper1_CostLedger
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper1_LedgerOfSource
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
set_option autoImplicit false
open Classical
open APFPaper1.Source

theorem APFPaper1.Foundation.feasible_ofSource {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) :
    Feasible (Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize) S ↔
      APFPaper1.Source.familyFeasible maintained sufficient usesToRealize S := by sorry
