-- Prove2me | Theorems.Thm_CompanionTheory_L3H_tSet_iff
-- name    : CompanionTheory.L3H.tSet_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:55:41.888389+00:00
-- url     : https://prove2.me/theorems/46c980a9-893e-5825-9977-bc29f2be643e
-- title:
--   L3 H: t Set iff
-- statement:
--   The L3 H construction uses the t Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L27-L36

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
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
variable (s : SplitPlace L) (n)
variable {n}

theorem CompanionTheory.L3H.tSet_iff {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) (x : Formalism.AUTREP.GAf L n) :
    x ∈ Formalism.AUTREP.tSet L n s ϖ k ↔ ∃ h ∈ DoubleCoset.doubleCoset (dg n s h0 k) (KL s n : Set _) (KL s n), emb s n h = x := by sorry
