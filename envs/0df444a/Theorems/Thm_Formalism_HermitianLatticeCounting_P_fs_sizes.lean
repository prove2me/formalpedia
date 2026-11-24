-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_sizes
-- name    : Formalism.HermitianLatticeCounting.P.fs_sizes
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:16.867217+00:00
-- url     : https://prove2.me/theorems/16f5f6ba-db2d-40f9-8268-afbb5078b93b
-- title:
--   P: fs sizes
-- statement:
--   The P construction uses the fs sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L237-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L237-L266

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
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
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.fs_sizes (C m M6 Q L kR lam : ℝ) (hC : 1 ≤ C) (hM64 : 64 ≤ M6) (hmM : m * m ≤ M6)
    (hQ : 0 ≤ Q) (hL2 : 1 / 2 ≤ L) (hk0 : 0 ≤ kR) (hlk : lam ≤ kR)
    (hyp : (16 * C + Q * Q) * M6 * L ≤ kR * lam) :
    8 ≤ kR ∧ m ≤ kR ∧ Q ≤ kR ∧ M6 ≤ 2 * (M6 * L) ∧ 16 * (M6 * L) ≤ kR * lam ∧
      16 * C * (M6 * L) ≤ kR * lam := by sorry
