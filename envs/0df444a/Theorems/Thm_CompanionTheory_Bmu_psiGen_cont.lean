-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_psiGen_cont
-- name    : CompanionTheory.Bmu.psiGen_cont
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:48.973737+00:00
-- url     : https://prove2.me/theorems/c868a5ab-5326-5d0e-9c1d-29aa996484fc
-- title:
--   Bmu: psi Gen cont
-- statement:
--   The Bmu construction uses the psi Gen cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/NormPsiGen.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/NormPsiGen.lean#L77-L88

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen
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
variable {k r : ℕ}

theorem CompanionTheory.Bmu.psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (PI.BesselMapUniq.psiGen k r z c) := by sorry
