-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_c_eq_sum
-- name    : Formalism.L2.Pj.QAt.TieQL.c_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:21.530469+00:00
-- url     : https://prove2.me/theorems/1a5ce422-19b4-4012-b44d-60f97baf8afa
-- title:
--   Tie QL: c eq sum
-- statement:
--   The Tie QL construction uses the c eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L30-L36

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

theorem Formalism.L2.Pj.QAt.TieQL.c_eq_sum (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (i : Fin ρ) (q : Q) :
    c i q = ∑ k, matA b c i k * b.repr q k := by sorry
