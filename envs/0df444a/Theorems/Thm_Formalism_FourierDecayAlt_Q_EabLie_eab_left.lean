-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_left
-- name    : Formalism.FourierDecayAlt.Q.EabLie.eab_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:23:22.970504+00:00
-- url     : https://prove2.me/theorems/f38b5f5f-4af2-4375-a7d8-53c3cab68995
-- title:
--   Eab Lie: eab left
-- statement:
--   The Eab Lie construction uses the eab left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L79-L88

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

theorem Formalism.FourierDecayAlt.Q.EabLie.eab_left (i : Fin (r + 1)) (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (hD : IsOpen D) (p q : Fin (mdim k r i)) (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (hL : LeftEq k r z i D f) :
    LeftEq k r z i D (EH k r (posL k r i p) (posL k r i q) f) := by sorry
