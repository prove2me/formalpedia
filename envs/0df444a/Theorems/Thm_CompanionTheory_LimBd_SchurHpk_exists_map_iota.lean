-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_map_iota
-- name    : CompanionTheory.LimBd.SchurHpk.exists_map_iota
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:27:51.903806+00:00
-- url     : https://prove2.me/theorems/19e5fb2e-cb0b-4fed-8dfd-15f5345fd855
-- title:
--   Schur Hpk: exists map iota
-- statement:
--   The Schur Hpk construction uses the exists map iota property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L121-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L121-L149

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

theorem CompanionTheory.LimBd.SchurHpk.exists_map_iota (hP : IsCayley k r ε P) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μG = Measure.map (iota (ε := ε) P) (c • muG ε) := by sorry
