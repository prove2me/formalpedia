-- Prove2me | Theorems.Thm_CompanionTheory_L3H_M0_fg
-- name    : CompanionTheory.L3H.M0_fg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:26.056968+00:00
-- url     : https://prove2.me/theorems/9fda8051-b161-5fdb-9850-3b80d9456624
-- title:
--   L3 H: M0 fg
-- statement:
--   The L3 H construction uses the M0 fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L55-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L55-L55

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
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
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}

theorem CompanionTheory.L3H.M0_fg (l : ℕ) [Fact l.Prime] (c : ℕ) : (M0 L l c).FG := by sorry
