-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_smul_top_prod
-- name    : Formalism.HermitianLatticeCounting.P.ideal_smul_top_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:54.116968+00:00
-- url     : https://prove2.me/theorems/f6a359d6-28bf-4289-b6e7-200a89e1d20e
-- title:
--   P: ideal smul top prod
-- statement:
--   The P construction uses the ideal smul top prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IdealsOfNormEqIndexSet.lean#L716-L735
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IdealsOfNormEqIndexSet.lean#L716-L735

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO

theorem Formalism.HermitianLatticeCounting.P.ideal_smul_top_prod {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (I : Ideal R) :
    I • (⊤ : Submodule R (M × N)) =
      (I • (⊤ : Submodule R M)).prod (I • (⊤ : Submodule R N)) := by sorry
