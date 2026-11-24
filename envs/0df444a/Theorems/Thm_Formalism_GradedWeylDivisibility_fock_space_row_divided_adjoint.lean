-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_row_divided_adjoint
-- name    : Formalism.GradedWeylDivisibility.fock_space_row_divided_adjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:38.592121+00:00
-- url     : https://prove2.me/theorems/4967567d-6620-456a-9bfa-7b1a9d1edb48
-- title:
--   Graded Weyl Divisibility: fock space row divided adjoint
-- statement:
--   The Graded Weyl Divisibility construction uses the fock space row divided adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L169-L173

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

theorem Formalism.GradedWeylDivisibility.fock_space_row_divided_adjoint : FockQRowDivAdj := by sorry
