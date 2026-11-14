-- Prove2me | Theorems.Thm_APFB05_overfull_chain_not_admissible
-- name    : APFB05.overfull_chain_not_admissible
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:58:14.630224+00:00
-- url     : https://prove2.me/theorems/3ea817e2-4e6c-4ae0-a619-cfc541bf45f9
-- title:
--   A support-novel chain cannot exceed its capacity budget
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. The guarded B05 hypothesis prices tested, support-novel additions only when both the starting and enlarged families are admissible. All resource, calibration, support and realization arguments are shared between this hypothesis and the conclusion. Assume B05 and a chain of n finite-family insertions, each of which adds a tested task that is support-novel over its preceding family. If capacity is strictly less than n times the positive floor, the final family is not admissible. The starting family need not be empty; the conclusion does not count arbitrary predicates or all members of a carrier. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFB05_capacity_forced_family.lean, declaration at line 56 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Classical
open APFPaper1.Source

namespace APFB05
end APFB05
open APFB05

theorem APFB05.overfull_chain_not_admissible
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (htested : ∀ i < n, tested g (d i))
    (hnovel : ∀ i < n, supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S i) (d i))
    (hover : C g < (n : ℝ) * epsilon g) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S n) := by sorry
