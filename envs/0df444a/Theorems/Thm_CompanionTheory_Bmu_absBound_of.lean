-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_absBound_of
-- name    : CompanionTheory.Bmu.absBound_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:16:21.196389+00:00
-- url     : https://prove2.me/theorems/39aaba9a-5151-5783-8066-5e9287d12f93
-- title:
--   Bmu: abs Bound of
-- statement:
--   The Bmu construction uses the abs Bound of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ProdNormLe.lean#L23-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ProdNormLe.lean#L23-L98

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ProdNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CompanionTheory.Bmu.absBound_of (hF : Factor) (hAd : DsAd) (hDer : DsDer) (hWB : WordBd) : AbsBound := by sorry
