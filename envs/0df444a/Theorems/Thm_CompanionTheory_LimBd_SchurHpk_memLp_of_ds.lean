-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_SchurHpk_memLp_of_ds
-- name    : CompanionTheory.LimBd.SchurHpk.memLp_of_ds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:52.797814+00:00
-- url     : https://prove2.me/theorems/1fa2a0c5-ebcf-49fd-9056-edb1e69a40a8
-- title:
--   Schur Hpk: mem Lp of ds
-- statement:
--   The Schur Hpk construction uses the mem Lp of ds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L211-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L211-L219

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
omit [CompleteSpace H]

theorem CompanionTheory.LimBd.SchurHpk.memLp_of_ds {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ)
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (v w : H) :
    MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ) 2 μG := by sorry
