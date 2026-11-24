-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_RL_apply
-- name    : Formalism.FourierDecayAlt.Q.TInvW.RL_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:51:48.224854+00:00
-- url     : https://prove2.me/theorems/45cc415a-1ba4-445f-b926-ad85e83b03a2
-- title:
--   TInv W: RL apply
-- statement:
--   The TInv W construction uses the RL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L360-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L360-L362

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

theorem Formalism.FourierDecayAlt.Q.TInvW.RL_apply (M M' : Module.End ℂ (Sm E k r i D)) (hM : M * RL (E := E) hP hC hD hs' hRS hs'G = RL (E := E) hP hC hD hs' hRS hs'G * M')
    (x : Sm E k r i D) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    (M (RL hP hC hD hs' hRS hs'G x)).1 ⟨g, hg⟩ = (M' x).1 ⟨g * s', hs' g hg⟩ := by sorry
