-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpart_mem
-- name    : Formalism.FourierDecayAlt.Q.EabLie.hpart_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:07:06.874908+00:00
-- url     : https://prove2.me/theorems/717c15d1-3da2-4e28-8871-fc40bbfcbe72
-- title:
--   Eab Lie: hpart mem
-- statement:
--   The Eab Lie construction uses the hpart mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L16-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.Q.EabLie.hpart_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) •
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) ∈ Glev k r i) ∧
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) •
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) ∈ Glev k r i) := by sorry
