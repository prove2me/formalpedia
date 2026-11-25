-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Irr_avg_right
-- name    : CompanionTheory.Mirab.Irr.avg_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:10.537117+00:00
-- url     : https://prove2.me/theorems/b467a954-a617-523e-bfc2-f8f218cbd8fc
-- title:
--   Irr: avg right
-- statement:
--   The Irr construction uses the avg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L69-L80

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

theorem CompanionTheory.Mirab.Irr.avg_right [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) (x : mirabSub k n)
    (v : uniSub k n) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * (v : mirabSub k n) * u) =
      (∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * u)) * genericChar n ψ₀ v := by sorry
