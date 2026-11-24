-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_exponent_inequality_degenerate_mid
-- name    : Formalism.HermitianLatticeCounting.P.exponent_inequality_degenerate_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:44.212009+00:00
-- url     : https://prove2.me/theorems/0d68367a-5d9d-4da1-bbfb-a4c3f9e1f273
-- title:
--   P: exponent inequality degenerate mid
-- statement:
--   The P construction uses the exponent inequality degenerate mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean#L238-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean#L238-L335

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

theorem Formalism.HermitianLatticeCounting.P.exponent_inequality_degenerate_mid (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (S lGam : ℝ) (hS2 : 2 ≤ S) (hSK : S ≤ K) (hG0 : 0 ≤ lGam)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    ((S - 2) * K * F) * (l2 - lg) + (C * M ^ 2 * F * L * C + S * K * F * lC) + K * F * lC +
      (C * M ^ 2 * F * L) * (C * (S + M) * M ^ 2) + 6 * S * F * (lC + 2 * lk) + lGam +
      C * M ^ 6 * F * L + K * F * (lC - lk) ≤ -(K * F * lk) / 2 - 2 * lGam - lk := by sorry
