-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_map_rowDiv
-- name    : Formalism.GradedWeylDivisibility.lfockq_map_rowDiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:02.629274+00:00
-- url     : https://prove2.me/theorems/b2d74d72-60a7-40a5-bb3f-6ed3a2fa3389
-- title:
--   Graded Weyl Divisibility: lfockq map row Div
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq map row Div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L164-L167

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

theorem Formalism.GradedWeylDivisibility.lfockq_map_rowDiv {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowDiv ℚ a b k f) = rowDiv ℂ a b k (map (Rat.castHom ℂ) f) := by sorry
