-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qminor_rep
-- name    : Formalism.FourierDecayAlt.Q.TInvW.qminor_rep
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:58:46.156471+00:00
-- url     : https://prove2.me/theorems/c9dc6506-257a-415e-ab05-9207c36890aa
-- title:
--   TInv W: qminor rep
-- statement:
--   The TInv W construction uses the qminor rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L263-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L263-L273

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

theorem Formalism.FourierDecayAlt.Q.TInvW.qminor_rep {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u F) (qminor (Ealg hP hC hD) a b u x).1 := by sorry
