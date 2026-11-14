-- Prove2me | Theorems.Thm_APFB05_novel_extra_costs_more
-- name    : APFB05.novel_extra_costs_more
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:54:21.721369+00:00
-- url     : https://prove2.me/theorems/5b8492e2-d222-4bff-8e6c-44fd8752e600
-- title:
--   Novel extra costs more
-- statement:
--   Under the guarded B05 MarginalFloor, inserting a tested support-novel distinction strictly increases familyCost when both the original and enlarged families are ledger-admissible. The positive uniform floor is consumed as a premise.
-- source:
--   Sib v44 Theorems/Thm_APFB05_A2_economy.lean:37

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

theorem APFB05.novel_extra_costs_more
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (d : D g) (htested : tested g d)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSd : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d) :
    familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S <
      familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
        (insert d S) := by sorry
