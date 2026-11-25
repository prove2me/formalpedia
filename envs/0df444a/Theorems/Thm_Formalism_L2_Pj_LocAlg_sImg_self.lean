-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_sImg_self
-- name    : Formalism.L2.Pj.LocAlg.sImg_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:36:08.874865+00:00
-- url     : https://prove2.me/theorems/06b73c39-7b7c-49d5-a688-6ac7027f4f75
-- title:
--   Loc Alg: s Img self
-- statement:
--   The Loc Alg construction uses the s Img self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L23-L28

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

theorem Formalism.L2.Pj.LocAlg.sImg_self (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) :
    sImg jc x (i, jc) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by sorry
