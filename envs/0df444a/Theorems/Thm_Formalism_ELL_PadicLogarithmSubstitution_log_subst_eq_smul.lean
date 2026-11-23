-- Prove2me | Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_log_subst_eq_smul
-- name    : Formalism.ELL.PadicLogarithmSubstitution.log_subst_eq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:41.555327+00:00
-- url     : https://prove2.me/theorems/5608851c-eb79-4f6f-ac29-1729f882763f
-- title:
--   Padic Logarithm Substitution: log subst eq smul
-- statement:
--   The Padic Logarithm Substitution construction uses the log subst eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L71-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L71-L95

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [Field K] [CharZero K]

theorem Formalism.ELL.PadicLogarithmSubstitution.log_subst_eq_smul (c : K) (B : PowerSeries K) (hB0 : constantCoeff B = 1)
    (hBd : (1 + X) * derivative K B = c • B) :
    (log K).subst (B - 1) = c • log K := by sorry
