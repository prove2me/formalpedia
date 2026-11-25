-- Prove2me | Theorems.Thm_CompanionTheory_L3H_heckeD_eq
-- name    : CompanionTheory.L3H.heckeD_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:57:47.033318+00:00
-- url     : https://prove2.me/theorems/de5851db-f8f3-5adf-8bca-6a3ab69e37fe
-- title:
--   L3 H: hecke D eq
-- statement:
--   The L3 H construction uses the hecke D eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L66-L70

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

theorem CompanionTheory.L3H.heckeD_eq (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {f : Formalism.AUTREP.GAf L n → W} (hf : Inv (emb s n) (KL s n) f)
    (d : GL (Fin n) (s.v.adicCompletion L⁺)) {D : Set (Formalism.AUTREP.GAf L n)}
    (hD : ∀ x, x ∈ D ↔ ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x) :
    NG.heckeD J D f = op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f := by sorry
