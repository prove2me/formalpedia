-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_exponent_inequality_single
-- name    : Formalism.HermitianLatticeCounting.P.exponent_inequality_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:10.295488+00:00
-- url     : https://prove2.me/theorems/673e25c9-98f8-4c65-88d7-f21b8d8fe231
-- title:
--   P: exponent inequality single
-- statement:
--   The P construction uses the exponent inequality single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean#L8-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean#L8-L70

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
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

theorem Formalism.HermitianLatticeCounting.P.exponent_inequality_single (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (R lGam : ℝ) (hR : 1 ≤ R) (hMR : M = 2 * R + 2)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    F * lC + (C * M ^ 2 * F * L) * (C * M ^ 3) + lGam + C * M ^ 6 * F * L +
      (K * F) * (lC - (2 * R + 1) * lg - R * lk) / 2 ≤ -(K * F * lk) := by sorry
