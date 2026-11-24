-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleMul
-- name    : Formalism.GradedWeylDivisibility.dualWeylModuleMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:52.956798+00:00
-- url     : https://prove2.me/theorems/c151b5cc-a5e3-4276-b532-540c67f7662d
-- title:
--   Graded Weyl Divisibility: dual Weyl Module Mul
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl Module Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylMul.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylMul.lean#L10-L11

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.dualWeylModuleMul : DualWeylMul := by sorry
