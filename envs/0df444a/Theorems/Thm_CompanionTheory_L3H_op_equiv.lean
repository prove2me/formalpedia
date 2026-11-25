-- Prove2me | Theorems.Thm_CompanionTheory_L3H_op_equiv
-- name    : CompanionTheory.L3H.op_equiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:10.013088+00:00
-- url     : https://prove2.me/theorems/7c011be9-f09b-5926-af95-c20bcade1be0
-- title:
--   L3 H: op equiv
-- statement:
--   The L3 H construction uses the op equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L77-L87

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

theorem CompanionTheory.L3H.op_equiv (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (hϖ : ∃ ϖ : s.v.adicCompletion L⁺, Valued.v ϖ = WithZero.exp (-1 : ℤ))
    {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (d : GL (Fin n) (s.v.adicCompletion L⁺)) (κ : J) (g) :
    op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f (g * κ) = ((χ κ : ℂˣ) : ℂ) • op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f g := by sorry
