-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_peelDecomposition
-- name    : Formalism.GradedWeylDivisibility.peelDecomposition
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:04.046816+00:00
-- url     : https://prove2.me/theorems/eef6be5e-7c51-4243-a89a-56cfd26915cc
-- title:
--   Graded Weyl Divisibility: peel Decomposition
-- statement:
--   The Graded Weyl Divisibility construction uses the peel Decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/PeelDecomp.lean#L9-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/PeelDecomp.lean#L9-L47

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpeelLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_PeelDecomp
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

theorem Formalism.GradedWeylDivisibility.peelDecomposition : PeelDecomp := by sorry
