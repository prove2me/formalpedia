-- Prove2me | Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
-- name    : Formalism.G.LogP.constantCoeff_subst_of_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:41.416801+00:00
-- url     : https://prove2.me/theorems/d06c1c5e-dca3-4b59-ac21-b8b6a73a70bc
-- title:
--   Log P: constant Coeff subst of zero
-- statement:
--   The Log P construction uses the constant Coeff subst of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L39-L54

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]

theorem Formalism.G.LogP.constantCoeff_subst_of_zero {σ τ : Type*} [Finite σ] [Finite τ]
    (Φ : MvPowerSeries σ R) {b : σ → MvPowerSeries τ R} (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (Φ.subst b) = constantCoeff Φ := by sorry
