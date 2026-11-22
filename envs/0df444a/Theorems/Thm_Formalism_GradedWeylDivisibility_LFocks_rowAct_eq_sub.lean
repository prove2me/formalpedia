-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_rowAct_eq_sub
-- name    : Formalism.GradedWeylDivisibility.LFocks_rowAct_eq_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:27.056416+00:00
-- url     : https://prove2.me/theorems/92086636-f832-4bda-a771-ac04fbd5eec5
-- title:
--   Graded Weyl Divisibility: LFocks row Act eq sub
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks row Act eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockRowAdj.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockRowAdj.lean#L14-L25

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
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

theorem Formalism.GradedWeylDivisibility.LFocks_rowAct_eq_sub {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    rowAct ℂ (n := n) g = sub (LFocks_rowMat g) := by sorry
