-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_trForm_nondeg
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.trForm_nondeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:18.296795+00:00
-- url     : https://prove2.me/theorems/99398393-b480-456d-821b-aa8c35370332
-- title:
--   Dual Lattice Index Bis: tr Form nondeg
-- statement:
--   The Dual Lattice Index Bis construction uses the tr Form nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L946-L956
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L946-L956

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

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.trForm_nondeg (h : U →ₗ[E] U →ₗ⋆[E] E) (hnd : ∀ x : U, (∀ y : U, h x y = 0) → x = 0) :
    ∀ x, (∀ y, trForm h x y = 0) → x = 0 := by sorry
