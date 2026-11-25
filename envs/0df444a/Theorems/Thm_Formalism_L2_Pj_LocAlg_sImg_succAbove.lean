-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_sImg_succAbove
-- name    : Formalism.L2.Pj.LocAlg.sImg_succAbove
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:36:59.79908+00:00
-- url     : https://prove2.me/theorems/a8315ed3-4e2b-45af-9bd1-104d8d64bb41
-- title:
--   Loc Alg: s Img succ Above
-- statement:
--   The Loc Alg construction uses the s Img succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L30-L35

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

theorem Formalism.L2.Pj.LocAlg.sImg_succAbove (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg jc x (i, jc.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by sorry
