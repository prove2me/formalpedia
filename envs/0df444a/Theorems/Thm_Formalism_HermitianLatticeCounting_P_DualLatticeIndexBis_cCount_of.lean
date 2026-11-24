-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_cCount_of
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.cCount_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:19.803508+00:00
-- url     : https://prove2.me/theorems/80dfd6c6-b2ba-4469-880a-25fab650c1c4
-- title:
--   Dual Lattice Index Bis: c Count of
-- statement:
--   The Dual Lattice Index Bis construction uses the c Count of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L493-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L493-L514

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

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.cCount_of (E : Type) [Field E] [NumberField E] (f D : ℕ) (e : ℝ)
    (hT : Nat.card (NumberField.Units.torsion E) ≤ 8 * f ^ 2)
    (hS : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard : ℕ) : ℝ) ≤ (D : ℝ) ^ e) :
    (cSet E D).Finite ∧ (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * e) := by sorry
