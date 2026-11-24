-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_LocalLatticeBases_weaker_displayed_bound
-- name    : Formalism.HermitianLattices.LocalLatticeBases.weaker_displayed_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:59:39.44111+00:00
-- url     : https://prove2.me/theorems/6bfd01a3-8ebb-4c77-a4e0-2b2fbd76cc39
-- title:
--   Local Lattice Bases: weaker displayed bound
-- statement:
--   The Local Lattice Bases construction uses the weaker displayed bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/FourierCommutesHeckeScalar.lean#L495-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/FourierCommutesHeckeScalar.lean#L495-L512

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset

theorem Formalism.HermitianLattices.LocalLatticeBases.weaker_displayed_bound : NonintegralMatrixPreservesThirdOverlattice := by sorry
