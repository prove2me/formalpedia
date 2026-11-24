-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_SchurHpk_forth_mem
-- name    : CompanionTheory.LimBd.SchurHpk.forth_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:46.791857+00:00
-- url     : https://prove2.me/theorems/79de5e73-3edd-416e-87b9-8eccc77c1649
-- title:
--   Schur Hpk: forth mem
-- statement:
--   The Schur Hpk construction uses the forth mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L73-L81

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

theorem CompanionTheory.LimBd.SchurHpk.forth_mem (hP : IsCayley k r ε P) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ UH (Hpk k r)) : P * x * P⁻¹ ∈ UJset ε := by sorry
