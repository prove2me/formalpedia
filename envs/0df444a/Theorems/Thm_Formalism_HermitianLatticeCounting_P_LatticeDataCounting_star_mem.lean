-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_star_mem
-- name    : Formalism.HermitianLatticeCounting.P.LatticeDataCounting.star_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:49.090383+00:00
-- url     : https://prove2.me/theorems/a41a5a83-8589-4431-bf0b-bacaa7967662
-- title:
--   Lattice Data Counting: star mem
-- statement:
--   The Lattice Data Counting construction uses the star mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L223-L224

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

theorem Formalism.HermitianLatticeCounting.P.LatticeDataCounting.star_mem (b : 𝓞 E) : star (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 E) E).range := by sorry
