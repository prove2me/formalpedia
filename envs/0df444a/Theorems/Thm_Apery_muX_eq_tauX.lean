-- Prove2me | Theorems.Thm_Apery_muX_eq_tauX
-- name    : Apery.muX_eq_tauX
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T19:34:24.923831+00:00
-- url     : https://prove2.me/theorems/53fe6735-2a8d-417b-84e0-6d77fee347ea
-- title:
--   The pullback identity: $\mu_X(P/D_K) = \tau_X((-1)^K x^5 P(-x^2))$
-- statement:
--   **The pullback identity (3.1).** For every $K$ and $P \in \mathbb{Q}[X]$, $\mu_X(P/D_K) = \tau_X\big((-1)^K x^5 P(-x^2)\big)$, where the right-hand side is the $\tau_X$-functional (`Apery.tauX`) evaluated on the pullback `pull K P` with the simple integer pole set $\{\pm 1, \dots, \pm K\}$ (`PlK K`). This is `muX_eq_tauX` of `Apery/Arith/Pullback.lean`; it converts every bound on $\mu_X$ into a bound on $\tau_X$, and is the key input of the small-prime bound `Apery.small_prime_bound` (hence `Apery.integral_mN`). **Formalization Note** `μX`, `tauX`, `pull`, `PlK` are platform definitions of `Zeta5_SourceConstruction`, `Zeta5_SourcePoleFun` and `Zeta5_SourcePullback`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/Pullback.lean#L1-L236 (+ PoleFun.lean, BinomBasis.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback

open Finset Polynomial

namespace Apery

theorem muX_eq_tauX (K : ℕ) (P : ℚ[X]) : μX K P = tauX (pull K P) (PlK K) := by
  sorry

end Apery
