-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_RL_inter
-- name    : Formalism.FourierDecayAlt.Q.TInvW.RL_inter
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:51:16.76553+00:00
-- url     : https://prove2.me/theorems/2e7334b5-41c0-49d3-8204-a56b524fcf84
-- title:
--   TInv W: RL inter
-- statement:
--   The TInv W construction uses the RL inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L341-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L341-L358

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
variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)
variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G
variable (hRt : StepRight)
include hRt

theorem Formalism.FourierDecayAlt.Q.TInvW.RL_inter (a b : Fin (mdim k r i)) :
    Ealg (E := E) hP hC hD a b * RL (E := E) hP hC hD hs' hRS hs'G =
      RL (E := E) hP hC hD hs' hRS hs'G * Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b := by sorry
