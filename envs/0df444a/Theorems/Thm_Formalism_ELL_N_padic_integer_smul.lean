-- Prove2me | Theorems.Thm_Formalism_ELL_N_padic_integer_smul
-- name    : Formalism.ELL.N_padic_integer_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:20.876626+00:00
-- url     : https://prove2.me/theorems/b518afac-89dc-4d7e-97e3-0fadb8340169
-- title:
--   ELL: N padic integer smul
-- statement:
--   The ELL construction uses the N padic integer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L150-L162

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
open Formalism.ELL
open PadicLogarithmSubstitution

theorem Formalism.ELL.N_padic_integer_smul : Formalism.ELL.NZpSmul := by sorry
