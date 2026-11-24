-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_fg_int
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.fg_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:12.346791+00:00
-- url     : https://prove2.me/theorems/21eb2e78-0f6b-4f3c-b71c-523ef9b37494
-- title:
--   Dual Lattice Index Bis: fg int
-- statement:
--   The Dual Lattice Index Bis construction uses the fg int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L992-L995
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L992-L995

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.fg_int (L : Submodule (𝓞 E) U) (hL : L.FG) : (L.restrictScalars ℤ).FG := by sorry
