-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Irr_sum_translate
-- name    : CompanionTheory.Mirab.Irr.sum_translate
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:13.451149+00:00
-- url     : https://prove2.me/theorems/8bd21e31-d67c-5cf6-b17f-f08eedb4ac82
-- title:
--   Irr: sum translate
-- statement:
--   The Irr construction uses the sum translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L94-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L94-L120

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

theorem CompanionTheory.Mirab.Irr.sum_translate (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) [Fintype (mirabSub k n)] [Fintype (uniSub k n)]
    (F g : mirabSub k n → ℂ) (hF : F ∈ MirabInducedSpace n ψ₀)
    (hr : ∀ (x : mirabSub k n) (u : uniSub k n), F (x * (u : mirabSub k n)) = F x * genericChar n ψ₀ u)
    (hg : g ∈ MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ∑ p : mirabSub k n, g p * F (x * p⁻¹) = (Nat.card (uniSub k n) : ℂ) * F 1 * g x := by sorry
