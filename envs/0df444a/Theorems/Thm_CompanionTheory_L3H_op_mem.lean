-- Prove2me | Theorems.Thm_CompanionTheory_L3H_op_mem
-- name    : CompanionTheory.L3H.op_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:31.977503+00:00
-- url     : https://prove2.me/theorems/03826507-3e35-4a66-a0f7-529ec3c7cf50
-- title:
--   L3 H: op mem
-- statement:
--   The L3 H construction uses the op mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L89-L100

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
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}

theorem CompanionTheory.L3H.op_mem (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (hϖ : ∃ ϖ : s.v.adicCompletion L⁺, Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hN : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1)
    {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (d : GL (Fin n) (s.v.adicCompletion L⁺)) :
    op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f ∈ NG.TypeSp ρ J χ := by sorry
