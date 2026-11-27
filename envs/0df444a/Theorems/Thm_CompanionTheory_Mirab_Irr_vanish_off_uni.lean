-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Irr_vanish_off_uni
-- name    : CompanionTheory.Mirab.Irr.vanish_off_uni
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:24.567219+00:00
-- url     : https://prove2.me/theorems/a391a4a7-afe9-4561-ba19-71834d639ded
-- title:
--   Irr: vanish off uni
-- statement:
--   The Irr construction uses the vanish off uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem CompanionTheory.Mirab.Irr.vanish_off_uni (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (f : mirabSub k n → ℂ)
    (hl : ∀ (u : uniSub k n) (x : mirabSub k n), f ((u : mirabSub k n) * x) = genericChar n ψ₀ u * f x)
    (hr : ∀ (x : mirabSub k n) (u : uniSub k n), f (x * (u : mirabSub k n)) = f x * genericChar n ψ₀ u)
    (h : mirabSub k n) (hh : h ∉ uniSub k n) : f h = 0 := by sorry
