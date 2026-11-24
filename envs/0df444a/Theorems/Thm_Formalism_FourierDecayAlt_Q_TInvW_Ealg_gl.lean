-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_Ealg_gl
-- name    : Formalism.FourierDecayAlt.Q.TInvW.Ealg_gl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:51:34.502996+00:00
-- url     : https://prove2.me/theorems/50fa6463-4736-4b19-87d5-5f761362ef1b
-- title:
--   TInv W: Ealg gl
-- statement:
--   The TInv W construction uses the Ealg gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L303-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L303-L316

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
variable (hG : EabGlLev)
include hG

theorem Formalism.FourierDecayAlt.Q.TInvW.Ealg_gl : GlRel (Ealg (E := E) (i := i) hP hC hD) := by sorry
