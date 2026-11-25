-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_inf_ker_eq_bot
-- name    : Formalism.L2.Pj.QAt.TieQL.inf_ker_eq_bot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:36:35.148799+00:00
-- url     : https://prove2.me/theorems/f77955ac-645a-4212-ab9d-1e4e645e7733
-- title:
--   Tie QL: inf ker eq bot
-- statement:
--   The Tie QL construction uses the inf ker eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L54-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean#L54-L80

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

theorem Formalism.L2.Pj.QAt.TieQL.inf_ker_eq_bot (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    LinearMap.range (coordK b) ⊓ (LinearMap.ker (cK b c)).restrictScalars O = ⊥ := by sorry
