-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_mat_conjTranspose
-- name    : Formalism.GradedWeylDivisibility.lfockq_mat_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:06.945809+00:00
-- url     : https://prove2.me/theorems/54092004-866c-4f01-979e-e252e37f832a
-- title:
--   Graded Weyl Divisibility: lfockq mat conj Transpose
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq mat conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L16-L23

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lfockq_mat_conjTranspose {r : ℕ} (a b : Fin r) (t : ℂ) :
    (lfockq_mat a b t).conjTranspose = lfockq_mat b a (star t) := by sorry
