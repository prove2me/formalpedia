-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_rdV_left
-- name    : Formalism.FourierDecayAlt.Q.EabLie.rdV_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:05.871043+00:00
-- url     : https://prove2.me/theorems/ea6a36c5-cb15-4077-a60b-8693e2db169c
-- title:
--   Eab Lie: rd V left
-- statement:
--   The Eab Lie construction uses the rd V left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L42-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/EabPresMain.lean#L42-L77

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

theorem Formalism.FourierDecayAlt.Q.EabLie.rdV_left (i : Fin (r + 1)) (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (hD : IsOpen D) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) (hL : LeftEq k r z i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) (n : Mx k r) (hn : n ∈ Nlev k r i) :
    RdV X f (n * g) = psi k r z cStd n • RdV X f g := by sorry
