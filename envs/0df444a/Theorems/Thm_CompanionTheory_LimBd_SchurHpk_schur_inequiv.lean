-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_SchurHpk_schur_inequiv
-- name    : CompanionTheory.LimBd.SchurHpk.schur_inequiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:14:45.348155+00:00
-- url     : https://prove2.me/theorems/0540347b-336c-4368-a2f5-9a956d193fb0
-- title:
--   Schur Hpk: schur inequiv
-- statement:
--   The Schur Hpk construction uses the schur inequiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L240-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L240-L275

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem CompanionTheory.LimBd.SchurHpk.schur_inequiv {k r : ℕ} {ε ε' : Fin (2 * r + k + 1) → Bool} {lam lam' : Fin (2 * r + k + 1) → ℝ}
    {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H' →L[ℂ] H')}
    (hds : IsDSHpk k r ε lam σ) (hds' : IsDSHpk k r ε' lam' σ')
    (hne : ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UH (Hpk k r), ∀ v, U (σ g v) = σ' g (U v))
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (v w : H) (v' w' : H') :
    Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ' (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ' (Matrix.of x) v'⟫_ℂ ∂μG = 0 := by sorry
