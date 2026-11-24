-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_PrimeNumberTheoremConsequences_PNTAPRelW_iff_ext
-- name    : Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW_iff_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:01:27.086283+00:00
-- url     : https://prove2.me/theorems/0063db20-dee7-4e55-933e-89662fe49cc2
-- title:
--   Prime Number Theorem Consequences: PNTAPRel W iff ext
-- statement:
--   The Prime Number Theorem Consequences construction uses the PNTAPRel W iff ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/MeanSquareOfPrimeNumberTheorem.lean#L12-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/MeanSquareOfPrimeNumberTheorem.lean#L12-L12

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfPrimeNumberTheoremInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqFinal
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BoxCountOfZeroDensity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BoxCountAllStatement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MeanSquareOfPrimeNumberTheorem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.PrimeNumberTheoremConsequences

theorem Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW_iff_ext : PNTAPRelW ↔ Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW := by sorry
