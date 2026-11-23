-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_mem_sup_span_iff
-- name    : Formalism.HermitianLatticeCounting.P.LatticeDataCounting.mem_sup_span_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:56.228111+00:00
-- url     : https://prove2.me/theorems/d79ab16a-d8cc-4d10-b986-d270c4e75066
-- title:
--   Lattice Data Counting: mem sup span iff
-- statement:
--   The Lattice Data Counting construction uses the mem sup span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L226-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L226-L238

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
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
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U]

theorem Formalism.HermitianLatticeCounting.P.LatticeDataCounting.mem_sup_span_iff {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] {n : ℕ} (N : Submodule R X)
    (t : Fin n → X) (x : X) :
    x ∈ N ⊔ Submodule.span R (Set.range t) ↔ ∃ c : Fin n → R, x - ∑ i, c i • t i ∈ N := by sorry
