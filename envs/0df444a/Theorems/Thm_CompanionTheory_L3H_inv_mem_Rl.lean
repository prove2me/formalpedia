-- Prove2me | Theorems.Thm_CompanionTheory_L3H_inv_mem_Rl
-- name    : CompanionTheory.L3H.inv_mem_Rl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:32.077011+00:00
-- url     : https://prove2.me/theorems/79a9c8f1-2cbe-5247-87b5-85fac49470b3
-- title:
--   L3 H: inv mem Rl
-- statement:
--   The L3 H construction uses the inv mem Rl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L32-L37

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}

theorem CompanionTheory.L3H.inv_mem_Rl {m : ℕ} (hm : ¬ l ∣ m) : ∃ r : Rl l, algebraMap (Rl l) ℂ r = (m : ℂ)⁻¹ := by sorry
