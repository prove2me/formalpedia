-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_det_mul_eq
-- name    : Formalism.L2.Pj.QAt.TieQL.det_mul_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:01.497321+00:00
-- url     : https://prove2.me/theorems/416c8bc2-b03b-4d9e-a9cf-6564371cadcf
-- title:
--   Tie QL: det mul eq
-- statement:
--   The Tie QL construction uses the det mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L48-L52

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

theorem Formalism.L2.Pj.QAt.TieQL.det_mul_eq (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q) :
    (Matrix.of fun i j => c i (th j)) = matA b c * Matrix.of fun k j => b.repr (th j) k := by sorry
