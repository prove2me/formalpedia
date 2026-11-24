-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_cSet_count
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.cSet_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:46.824794+00:00
-- url     : https://prove2.me/theorems/697bb87a-96bd-4b90-b00c-56ec0a900e56
-- title:
--   Dual Lattice Index Bis: c Set count
-- statement:
--   The Dual Lattice Index Bis construction uses the c Set count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L435-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L435-L491

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

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.cSet_count (E : Type) [Field E] [NumberField E] (D : ℕ)
    (hS : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.Finite) :
    (cSet E D).Finite ∧ (cSet E D).ncard ≤ Nat.card (NumberField.Units.torsion E) *
      {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard ^ 2 := by sorry
