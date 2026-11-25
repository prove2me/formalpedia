-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_aeval_qj
-- name    : Formalism.L2.Pj.LocAlg.aeval_qj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:59.04281+00:00
-- url     : https://prove2.me/theorems/a307ac23-c258-565a-aa88-f4a40cdc5f32
-- title:
--   Loc Alg: aeval qj
-- statement:
--   The Loc Alg construction uses the aeval qj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L71-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L71-L94

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}

theorem Formalism.L2.Pj.LocAlg.aeval_qj (hy0 : yv jc x j0 ≠ 0) (p : TVar D N) :
    aeval (tj jc j0 x) (qj jc j0 x p) = sImg jc x p := by sorry
