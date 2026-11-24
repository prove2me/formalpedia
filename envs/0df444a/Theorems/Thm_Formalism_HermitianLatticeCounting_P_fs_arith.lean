-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_arith
-- name    : Formalism.HermitianLatticeCounting.P.fs_arith
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:21.259231+00:00
-- url     : https://prove2.me/theorems/fb8d9c96-69fc-4d66-b856-318d025481c5
-- title:
--   P: fs arith
-- statement:
--   The P construction uses the fs arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L268-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L268-L299

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

theorem Formalism.HermitianLatticeCounting.P.fs_arith (C M6 L kR fR lam lC : ℝ) (hf1 : 1 ≤ fR) (hk8 : 8 ≤ kR) (hl0 : 0 ≤ lam)
    (hmE : M6 ≤ 2 * (M6 * L)) (hE16 : 16 * (M6 * L) ≤ kR * lam) (hCE : 16 * C * (M6 * L) ≤ kR * lam)
    (hlogC : 16 * lC ≤ lam) :
    M6 + (C * M6 * fR * L + C * M6 * fR * L) +
      ((kR - 2) * fR * (lC - lam) + (kR - 2) * fR * (lC - lam)) ≤ -(kR * fR * lam) := by sorry
