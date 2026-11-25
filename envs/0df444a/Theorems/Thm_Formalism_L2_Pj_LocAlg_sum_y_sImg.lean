-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_sum_y_sImg
-- name    : Formalism.L2.Pj.LocAlg.sum_y_sImg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:02.755983+00:00
-- url     : https://prove2.me/theorems/d170ee77-fb8f-4731-8187-8861fa384840
-- title:
--   Loc Alg: sum y s Img
-- statement:
--   The Loc Alg construction uses the sum y s Img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L37-L44

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

theorem Formalism.L2.Pj.LocAlg.sum_y_sImg (jc : Fin (N + 1)) (x : Fin N → Ω) {i : Fin (D + 1)} (hi : i ≠ 0) :
    ∑ j, algebraMap Ω (OmS Ω D N) (yv jc x j) * sImg jc x (i, j) = 0 := by sorry
