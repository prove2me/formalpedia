-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_class_admissible
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.class_admissible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:41.664552+00:00
-- url     : https://prove2.me/theorems/2049646d-2612-4429-86b7-b45e19ab54b8
-- title:
--   Zero Free Region GL2: class admissible
-- statement:
--   The Zero Free Region GL2 construction uses the class admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L286-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L286-L337

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.class_admissible : ClassAdmissible := by sorry
