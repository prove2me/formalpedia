-- Prove2me | Theorems.Thm_APFPaper1_Source_not_supportNovel_of_carried
-- name    : APFPaper1.Source.not_supportNovel_of_carried
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:05:04.317074+00:00
-- url     : https://prove2.me/theorems/4ea50266-697b-40b3-9400-f2378d5a5471
-- title:
--   Support already carried by every serving protocol is not novel
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. Suppose S has a serving protocol. If every protocol serving S already maintains some sufficient support for r, then r is not support-novel over S. The sufficient support for r need not be shown to be used to realize it: that extra requirement belongs to serving S, whereas novelty tests carried sufficient support. The positive-window contradiction uses a near-infimal serving protocol rather than assuming a minimum exists. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFB05_relation_task.lean, declaration at line 32 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source

theorem APFPaper1.Source.not_supportNovel_of_carried
    {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (r : D)
    (hfeas : familyFeasible maintained sufficient usesToRealize S)
    (hcarried : ∀ p : P,
      (∀ e ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma) →
      ∃ sigma : Set Record, sigma ⊆ maintained p ∧ sufficient p sigma r) :
    ¬ supportNovel wholeResource calibration maintained sufficient usesToRealize S r := by sorry
