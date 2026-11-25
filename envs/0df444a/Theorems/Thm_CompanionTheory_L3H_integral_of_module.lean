-- Prove2me | Theorems.Thm_CompanionTheory_L3H_integral_of_module
-- name    : CompanionTheory.L3H.integral_of_module
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:12.181081+00:00
-- url     : https://prove2.me/theorems/9b8769b9-a1a7-450e-ae2b-1886d8336d92
-- title:
--   L3 H: integral of module
-- statement:
--   The L3 H construction uses the integral of module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean#L139-L141

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
variable {R : Type} [CommRing R] [Algebra R ℂ]

theorem CompanionTheory.L3H.integral_of_module [Module R W] [IsScalarTower R ℂ W] [IsNoetherianRing R] (N : Submodule R W) (hN : N ≠ ⊥)
    (hfg : N.FG) (ν : ℂ) (hν : ∀ w ∈ N, ν • w ∈ N) : IsIntegral R ν := by sorry
