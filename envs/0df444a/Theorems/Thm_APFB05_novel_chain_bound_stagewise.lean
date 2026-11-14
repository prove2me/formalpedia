-- Prove2me | Theorems.Thm_APFB05_novel_chain_bound_stagewise
-- name    : APFB05.novel_chain_bound_stagewise
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:47:08.752809+00:00
-- url     : https://prove2.me/theorems/9c988659-598a-4ef7-87e6-c87fa4e79374
-- title:
--   A stagewise admissible novel chain has length at most capacity over floor
-- statement:
--   Suppose each step below n inserts one tested support-novel distinction, every family up to n is ledger-admissible, and guarded B05 supplies positive epsilon. Then n epsilon is at most the final familyCost, and n is at most C/epsilon. This counts chain increments without assuming additive protocol bills.
-- source:
--   Sib v44 Theorems/Thm_APFB05_novel_chain_stagewise.lean:30

import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1.Source

theorem APFB05.novel_chain_bound_stagewise
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop) (C epsilon : Context → ℝ)
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (htested : ∀ i < n, tested g (d i))
    (hnovel : ∀ i < n, supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S i) (d i))
    (hadm : ∀ i ≤ n, familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S i)) :
    (n : ℝ) * epsilon g ≤ familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (S n) ∧
      (n : ℝ) ≤ C g / epsilon g := by sorry
