-- Prove2me | Theorems.Thm_APFPaper1_Foundation_supportNovel_ofSource
-- name    : APFPaper1.Foundation.supportNovel_ofSource
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:21:50.874225+00:00
-- url     : https://prove2.me/theorems/2283b631-8a14-473e-be0b-7be2232e67ca
-- title:
--   Support novelty on the source ledger is source support novelty
-- statement:
--   Fix the same source data on both sides of the source-ledger adapter. Assume the designated null protocol has zero calibrated whole-resource bill. For every finite family $S$ and distinction $d$,
--
--   $$\operatorname{SupportNovel}(L,S,d)\ \Longleftrightarrow\ \operatorname{supportNovel}(S,d).$$
--
--   This identifies the positive near-optimal-window predicates using the price and family-cost bridge. It does not assert that any particular distinction is novel, tested or physically realized.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Theorems.Thm_APFPaper1_Foundation_supportNovel_ofSource; source SHA256 ca9a2528c0b1ad29446f9cc80c5b9b5aa411f38b159480de7fb3432635dd2c90. See the source header for original v9.27 line references and the November 11 testedness ruling.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper1_LedgerOfSource
import Definitions.Def_APFPaper1_SupportNovel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
set_option autoImplicit false
open Classical
open APFPaper1.Source

theorem APFPaper1.Foundation.supportNovel_ofSource {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop)
    (hnull : calibration (wholeResource p0) = 0) (S : Finset D) (d : D) :
    SupportNovel (Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize) S d ↔
      APFPaper1.Source.supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by sorry
