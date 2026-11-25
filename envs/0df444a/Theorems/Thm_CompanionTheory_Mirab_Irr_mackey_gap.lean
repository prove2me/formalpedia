-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Irr_mackey_gap
-- name    : CompanionTheory.Mirab.Irr.mackey_gap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:18.827079+00:00
-- url     : https://prove2.me/theorems/b38febd8-d849-5ef3-9980-ec67f8b6d139
-- title:
--   Irr: mackey gap
-- statement:
--   The Irr construction uses the mackey gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L13-L17

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

theorem CompanionTheory.Mirab.Irr.mackey_gap (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (h : mirabSub k n) (hh : h ∉ uniSub k n) :
    ∃ u c : uniSub k n, (c : mirabSub k n) = h⁻¹ * u * h ∧ genericChar n ψ₀ c ≠ genericChar n ψ₀ u := by sorry
