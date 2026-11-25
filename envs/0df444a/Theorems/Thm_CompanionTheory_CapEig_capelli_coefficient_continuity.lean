-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_capelli_coefficient_continuity
-- name    : CompanionTheory.CapEig.capelli_coefficient_continuity
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:17:01.872878+00:00
-- url     : https://prove2.me/theorems/aecf4164-12cf-52b0-a7ca-b86f863f0517
-- title:
--   Cap Eig: capelli coefficient continuity
-- statement:
--   The Cap Eig construction uses the capelli coefficient continuity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefCC.lean#L78-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefCC.lean#L78-L136

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefCC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CompanionTheory.CapEig.capelli_coefficient_continuity : CoefCC := by sorry
