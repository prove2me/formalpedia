-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_unitary
-- name    : Formalism.FourierDecayAlt.P.Ux4.Rn_unitary
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:59:09.802611+00:00
-- url     : https://prove2.me/theorems/a1471226-0736-4935-9b96-afd42a597d51
-- title:
--   Ux4: Rn unitary
-- statement:
--   The Ux4 construction uses the Rn unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L288-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L288-L300

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux4.Rn_unitary (x : RC k j ρ) : (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ) := by sorry
