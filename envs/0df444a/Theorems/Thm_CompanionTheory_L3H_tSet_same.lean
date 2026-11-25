-- Prove2me | Theorems.Thm_CompanionTheory_L3H_tSet_same
-- name    : CompanionTheory.L3H.tSet_same
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:58:37.454657+00:00
-- url     : https://prove2.me/theorems/4db9799d-b85d-48b6-b794-75f14aa79c42
-- title:
--   L3 H: t Set same
-- statement:
--   The L3 H construction uses the t Set same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L108-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L108-L131

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
variable {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}

theorem CompanionTheory.L3H.tSet_same (s s' : SplitPlace L) (hv : s'.v = s.v) {ϖ' : s'.v.adicCompletion L⁺} (h0 : ϖ' ≠ 0) (k : ℕ) :
    ∃ d : GL (Fin n) (s.v.adicCompletion L⁺), ∀ x, x ∈ Formalism.AUTREP.tSet L n s' ϖ' k ↔
      ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x := by sorry
