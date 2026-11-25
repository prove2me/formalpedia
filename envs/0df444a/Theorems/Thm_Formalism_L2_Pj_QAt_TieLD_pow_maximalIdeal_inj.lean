-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_pow_maximalIdeal_inj
-- name    : Formalism.L2.Pj.QAt.TieLD.pow_maximalIdeal_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:44.782544+00:00
-- url     : https://prove2.me/theorems/1d66a591-ceab-4ec5-b3fd-0e078d8ceac8
-- title:
--   Tie LD: pow maximal Ideal inj
-- statement:
--   The Tie LD construction uses the pow maximal Ideal inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L15-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR

theorem Formalism.L2.Pj.QAt.TieLD.pow_maximalIdeal_inj {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    {a b : ℕ} (h : IsLocalRing.maximalIdeal T ^ a = IsLocalRing.maximalIdeal T ^ b) : a = b := by sorry
