-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_semistandard_index_finite
-- name    : Formalism.GradedWeylDivisibility.semistandard_index_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:51.033795+00:00
-- url     : https://prove2.me/theorems/bf72287a-749c-49be-a9a0-31778dd64aae
-- title:
--   Graded Weyl Divisibility: semistandard index finite
-- statement:
--   The Graded Weyl Divisibility construction uses the semistandard index finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SSIdxFinite.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SSIdxFinite.lean#L18-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSIdxFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.semistandard_index_finite : SSIdxFinite := by sorry
