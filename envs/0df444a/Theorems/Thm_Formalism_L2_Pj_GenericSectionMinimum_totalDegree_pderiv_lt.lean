-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_totalDegree_pderiv_lt
-- name    : Formalism.L2.Pj.GenericSectionMinimum.totalDegree_pderiv_lt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:29.957803+00:00
-- url     : https://prove2.me/theorems/ac34c5c3-463a-5d70-89b5-258117383013
-- title:
--   Generic Section Minimum: total Degree pderiv lt
-- statement:
--   The Generic Section Minimum construction uses the total Degree pderiv lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L69-L86

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_totalDegree_pderiv_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]

theorem Formalism.L2.Pj.GenericSectionMinimum.totalDegree_pderiv_lt {E : Type} [CommRing E] {σ : Type} (p : MvPolynomial σ E) (i : σ)
    (h : MvPolynomial.pderiv i p ≠ 0) : (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by sorry
