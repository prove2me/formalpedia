-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_coordK_injective
-- name    : Formalism.L2.Pj.QAt.TieQL.coordK_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:36:20.432319+00:00
-- url     : https://prove2.me/theorems/6fd61ce2-955a-4f47-8c27-383a24f7e7aa
-- title:
--   Tie QL: coord K injective
-- statement:
--   The Tie QL construction uses the coord K injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L18-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieQL
open Module
variable {O Q : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup Q] [Module O Q] {ρ : ℕ}

theorem Formalism.L2.Pj.QAt.TieQL.coordK_injective (b : Basis (Fin ρ) O Q) : Function.Injective (coordK b) := by sorry
