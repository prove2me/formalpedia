-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_totient_odd
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.totient_odd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:03.710289+00:00
-- url     : https://prove2.me/theorems/2a0267fb-6ae2-418b-9413-40dfb450f8a3
-- title:
--   Dual Lattice Index Bis: totient odd
-- statement:
--   The Dual Lattice Index Bis construction uses the totient odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L144-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L144-L174

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

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.totient_odd : ∀ n : ℕ, Odd n → n ≤ Nat.totient n ^ 2 := by sorry
