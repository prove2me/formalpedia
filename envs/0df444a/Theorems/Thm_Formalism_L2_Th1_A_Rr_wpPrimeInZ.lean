-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Rr_wpPrimeInZ
-- name    : Formalism.L2.Th1.A.Rr.wpPrimeInZ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:19:39.593638+00:00
-- url     : https://prove2.me/theorems/7cf370f5-4515-4411-86b8-db797ac11102
-- title:
--   Rr: wp Prime In Z
-- statement:
--   The Rr construction uses the wp Prime In Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WeierstrassPPrimeUnit.lean#L17-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WeierstrassPPrimeUnit.lean#L17-L36

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WeierstrassPPrimeUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Rr
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem Formalism.L2.Th1.A.Rr.wpPrimeInZ : expSer W ^ 3 * (-2 + X ^ 3 * derivative K (wpReg W))
    = X ^ 3 * (-2 * (xS W).subst (expSer W) + C W.a₁ * expSer W * (xS W).subst (expSer W)
        + C W.a₃ * expSer W ^ 3) := by sorry
