-- Prove2me | Theorems.Thm_APFB05_realized_has_no_removable_novel
-- name    : APFB05.realized_has_no_removable_novel
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:55:29.740546+00:00
-- url     : https://prove2.me/theorems/996812b3-1e24-45aa-adfb-1fdb3d9d3dd3
-- title:
--   Realized has no removable novel
-- statement:
--   Under guarded B05, suppose actual minimizes familyCost over a supplied family set containing S. If d is tested and support-novel over S and both S and insert d S are ledger-admissible, then actual is not insert d S. This uses the explicitly supplied family minimum, not a certified physical A2 binding.
-- source:
--   Sib v44 Theorems/Thm_APFB05_A2_economy.lean:54

import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source


variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

theorem APFB05.realized_has_no_removable_novel
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (families : Set (Finset (D g))) (actual : Finset (D g))
    (hA2 : actual ∈ families ∧ ∀ a ∈ families,
      familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
          actual ≤
        familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) a)
    (S : Finset (D g)) (d : D g) (hSmem : S ∈ families) (htested : tested g d)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSd : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d) :
    actual ≠ insert d S := by sorry
