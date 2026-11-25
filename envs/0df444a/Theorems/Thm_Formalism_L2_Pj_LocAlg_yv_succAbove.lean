-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_yv_succAbove
-- name    : Formalism.L2.Pj.LocAlg.yv_succAbove
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:08.169362+00:00
-- url     : https://prove2.me/theorems/0ec55d53-a669-4d62-9db2-d2898d0cd92e
-- title:
--   Loc Alg: yv succ Above
-- statement:
--   The Loc Alg construction uses the yv succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L19-L21

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

theorem Formalism.L2.Pj.LocAlg.yv_succAbove (jc : Fin (N + 1)) (x : Fin N → Ω) (k : Fin N) : yv jc x (jc.succAbove k) = x k := by sorry
