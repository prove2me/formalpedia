-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_eq_of_capelliPolynomial_eq
-- name    : CompanionTheory.CapEig.eq_of_capelliPolynomial_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:44:14.810146+00:00
-- url     : https://prove2.me/theorems/4a701592-4772-4af9-b279-14727abcf659
-- title:
--   Cap Eig: eq of capelli Polynomial eq
-- statement:
--   The Cap Eig construction uses the eq of capelli Polynomial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/BetaAtInfinityZero.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/BetaAtInfinityZero.lean#L40-L52

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

theorem CompanionTheory.CapEig.eq_of_capelliPolynomial_eq {n : ℕ} {μ μ' : Fin n → ℝ} (hμ : StrictAnti μ) (hμ' : StrictAnti μ')
    (h : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (μ' s : ℂ)) Y) : μ = μ' := by sorry
