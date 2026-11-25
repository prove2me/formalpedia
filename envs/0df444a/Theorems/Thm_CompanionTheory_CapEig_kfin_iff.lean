-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_kfin_iff
-- name    : CompanionTheory.CapEig.kfin_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:23.867642+00:00
-- url     : https://prove2.me/theorems/88860a22-d56b-4009-9f07-1c6636ba0b76
-- title:
--   Cap Eig: kfin iff
-- statement:
--   The Cap Eig construction uses the kfin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/BetaAtInfinityZero.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/BetaAtInfinityZero.lean#L13-L38

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt MeasureTheory CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig

theorem CompanionTheory.CapEig.kfin_iff (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : B.Mat k r) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) (hP : IsCayleyU k r ε P) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by sorry
