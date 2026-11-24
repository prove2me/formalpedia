-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_lin
-- name    : Formalism.FourierDecayAlt.Q.EabLie.eab_lin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:24:08.379782+00:00
-- url     : https://prove2.me/theorems/e1d5c006-3892-450f-aa7e-bccb27c4cf01
-- title:
--   Eab Lie: eab lin
-- statement:
--   The Eab Lie construction uses the eab lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L90-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L90-L122

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

theorem Formalism.FourierDecayAlt.Q.EabLie.eab_lin (i : Fin (r + 1)) (D : Set (Mx k r)) (p q : Fin (mdim k r i))
    (f f₂ : Mx k r → E) (s : ℂ) (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) (fun x => f x + s • f₂ x) g =
      EH k r (posL k r i p) (posL k r i q) f g + s • EH k r (posL k r i p) (posL k r i q) f₂ g := by sorry
