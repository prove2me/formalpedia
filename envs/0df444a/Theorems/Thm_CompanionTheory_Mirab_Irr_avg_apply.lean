-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Irr_avg_apply
-- name    : CompanionTheory.Mirab.Irr.avg_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:02.83301+00:00
-- url     : https://prove2.me/theorems/49126e05-3615-5605-9181-879ba05d52fc
-- title:
--   Irr: avg apply
-- statement:
--   The Irr construction uses the avg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L61-L67

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

theorem CompanionTheory.Mirab.Irr.avg_apply [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ((∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) • mirabInduced n ψ₀ (u : mirabSub k n) f :
        MirabInducedSpace n ψ₀) : mirabSub k n → ℂ) x =
      ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * (f : mirabSub k n → ℂ) (x * u) := by sorry
