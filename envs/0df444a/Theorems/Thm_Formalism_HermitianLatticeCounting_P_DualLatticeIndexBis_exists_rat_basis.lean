-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_rat_basis
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_rat_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:50.473092+00:00
-- url     : https://prove2.me/theorems/0a5feedc-d0c0-4c88-b6e6-f46393ae8d6b
-- title:
--   Dual Lattice Index Bis: exists rat basis
-- statement:
--   The Dual Lattice Index Bis construction uses the exists rat basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L684-L706
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L684-L706

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

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_rat_basis {V ι : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V] (L : Submodule ℤ V)
    (c : Module.Basis ι ℤ L) (hL : ∀ x : V, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L) :
    ∃ cb : Module.Basis ι ℚ V, (∀ i, cb i = (c i : V)) ∧ L = Submodule.span ℤ (Set.range cb) := by sorry
