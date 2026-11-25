-- Prove2me | Theorems.Thm_CompanionTheory_L3H_eig_int
-- name    : CompanionTheory.L3H.eig_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:15.404132+00:00
-- url     : https://prove2.me/theorems/21d78541-41e2-56bc-b34d-b7c6342180ba
-- title:
--   L3 H: eig int
-- statement:
--   The L3 H construction uses the eig int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L93-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L93-L176

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

theorem CompanionTheory.L3H.eig_int (alg : Formalism.AUTREP.IsAlgWeight L n ρ) (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {l : ℕ} [hl' : Fact l.Prime]
    (hsl : ¬ s.Above l) (d : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) {f : Formalism.AUTREP.GAf L n → W}
    (hf : f ∈ NG.TypeSp ρ J χ) (hf0 : f ≠ 0) (ν : ℂ)
    (hν : op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f = ν • f) : IsIntegral (Rl l) ν := by sorry
