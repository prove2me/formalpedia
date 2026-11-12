-- Prove2me | Theorems.Thm_APFPaper1_Foundation_cost_ofSource
-- name    : APFPaper1.Foundation.cost_ofSource
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:20:20.869743+00:00
-- url     : https://prove2.me/theorems/9c607c59-9039-4b29-8d2b-9734a237e6e1
-- title:
--   The infimal cost of the source ledger is the family cost
-- statement:
--   Fix the source protocol/support data and a designated protocol $p_0$ whose calibrated whole-resource bill is zero. Let $L$ be the corresponding source ledger. Then for every finite family $S$,
--
--   $$\operatorname{cost}(L,S)=\kappa(S).$$
--
--   The explicit zero-bill hypothesis makes the ledger's protocol price equal the original calibrated bill everywhere; their sets of serving-protocol prices coincide. This is equality of real-valued infima, including the empty-set convention. Interpreting either side as a physical enforceable cost still requires feasibility; no minimizer is asserted.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Theorems.Thm_APFPaper1_Foundation_cost_ofSource; source SHA256 ecabd6531d0972516ec19157d9ecb3de92edaecb6965eb253a1f55d17901cd02. See the source header for original v9.27 line references and the November 11 testedness ruling.

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

theorem APFPaper1.Foundation.cost_ofSource {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop)
    (hnull : calibration (wholeResource p0) = 0) (S : Finset D) :
    cost (Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize) S =
      APFPaper1.Source.familyCost wholeResource calibration maintained sufficient usesToRealize S := by sorry
