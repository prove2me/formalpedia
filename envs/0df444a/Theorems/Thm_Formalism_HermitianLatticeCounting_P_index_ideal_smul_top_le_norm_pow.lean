-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_index_ideal_smul_top_le_norm_pow
-- name    : Formalism.HermitianLatticeCounting.P.index_ideal_smul_top_le_norm_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:57.632911+00:00
-- url     : https://prove2.me/theorems/d0d7680a-5992-4107-86b3-2d51659e7b70
-- title:
--   P: index ideal smul top le norm pow
-- statement:
--   The P construction uses the index ideal smul top le norm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IdealsOfNormEqIndexSet.lean#L553-L661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IdealsOfNormEqIndexSet.lean#L553-L661

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

theorem Formalism.HermitianLatticeCounting.P.index_ideal_smul_top_le_norm_pow {E : Type} [Field E] [NumberField E] (p : Ideal (𝓞 E)) [hp : p.IsMaximal] (hp0 : p ≠ ⊥)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (k : ℕ) (htf : TF E X)
    (hli : LIB E X k) :
    (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≠ 0 ∧
      (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≤ Ideal.absNorm p ^ k := by sorry
