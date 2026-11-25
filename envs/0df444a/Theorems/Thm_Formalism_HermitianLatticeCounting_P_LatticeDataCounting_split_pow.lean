-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_split_pow
-- name    : Formalism.HermitianLatticeCounting.P.LatticeDataCounting.split_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:15.66138+00:00
-- url     : https://prove2.me/theorems/c9a7cbe3-0d67-48d5-adeb-85399cdfdc96
-- title:
--   Lattice Data Counting: split pow
-- statement:
--   The Lattice Data Counting construction uses the split pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L307-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L307-L308

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

theorem Formalism.HermitianLatticeCounting.P.LatticeDataCounting.split_pow (i' : ℝ) (hi : 1 ≤ i') (k : ℕ) (c : ℝ) : i' ^ ((k : ℝ) + c) = i' ^ k * i' ^ c := by sorry
