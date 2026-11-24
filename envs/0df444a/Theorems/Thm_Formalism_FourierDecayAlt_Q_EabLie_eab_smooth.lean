-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_smooth
-- name    : Formalism.FourierDecayAlt.Q.EabLie.eab_smooth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:23:41.376261+00:00
-- url     : https://prove2.me/theorems/51a2409c-7ef8-4e65-a4f1-ebd8f06f8720
-- title:
--   Eab Lie: eab smooth
-- statement:
--   The Eab Lie construction uses the eab smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L23-L40

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

theorem Formalism.FourierDecayAlt.Q.EabLie.eab_smooth (i : Fin (r + 1)) (D : Set (Mx k r)) (p q : Fin (mdim k r i))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (EH k r (posL k r i p) (posL k r i q) f) := by sorry
