-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_second_capelli_minor_represents
-- name    : Formalism.FourierDecayAlt.Q.TInvW.second_capelli_minor_represents
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:33.048813+00:00
-- url     : https://prove2.me/theorems/4b7908d7-f0f0-4a30-8b9d-e14d74e480ba
-- title:
--   TInv W: second capelli minor represents
-- statement:
--   The TInv W construction uses the second capelli minor represents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L284-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L284-L295

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD

theorem Formalism.FourierDecayAlt.Q.TInvW.second_capelli_minor_represents (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' F g =
      (chat2A (Ealg hP hC hD) u (a g) (a' g) (β g) (β' g) x).1 ⟨g, hg⟩ := by sorry
