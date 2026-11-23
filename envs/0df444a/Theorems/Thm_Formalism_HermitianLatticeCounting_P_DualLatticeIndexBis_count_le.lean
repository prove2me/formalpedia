-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_count_le
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.count_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:27.119691+00:00
-- url     : https://prove2.me/theorems/796e7166-cf74-475c-a15a-37695ec3db40
-- title:
--   Dual Lattice Index Bis: count le
-- statement:
--   The Dual Lattice Index Bis construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L354-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L354-L399

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

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.count_le (E : Type) [Field E] [NumberField E] (N k y : ℕ) (hN : 1 ≤ N)
    (hOm : Formalism.SLP.OmegaPow)
    (h : ∀ n, 1 ≤ n → {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.Finite ∧
      {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤ N ^ (Nat.primeFactorsList n).length * n ^ k) :
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + ((k : ℝ) + Real.logb 2 N)) := by sorry
