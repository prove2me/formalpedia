-- Prove2me | Theorems.Thm_Apery_small_prime_bound
-- name    : Apery.small_prime_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T19:07:18.834927+00:00
-- url     : https://prove2.me/theorems/4211762e-37e2-4162-be75-d6da67f753e6
-- title:
--   Small-prime bound: $v_p(F_K) \ge -(6\cdot 37n \log_p 200n + 37n \cdot v_p(24))$
-- statement:
--   **Small-prime bound (3.12).** For every prime $p$ with $pM \le K = 40n$ (all $p$ when $n \ge 1$ up to the cutoff) the Gauss valuation of $F_K$ is at least $-(6 \cdot 37n \cdot \log_p(200n) + 37n \cdot v_p(24))$. This is `small_prime_bound` of `Apery/Arith/SmallPrimeF.lean`; it combines the Legendre/valuation bookkeeping (`Legendre.lean`, `vS_eq`), the binomial-basis integer-window lemma `VG_eval_int_of_window` and the change of basis `det_basis_change`. Together with `inner_bound_cap` and `outer_bound` it gives the local exponent `Lp` of the normaliser `mN` (`Apery.integral_mN`). **Formalization Note** `GV`, `F` are platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/SmallPrimeF.lean#L201-L283 (+ SmallPrimeTau.lean, TauBound.lean, BinomBasis.lean, Legendre.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem small_prime_bound {n : ℕ} (hn : 1 ≤ n) :
    GV p (F n) (-(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℚ) + (37 * n : ℕ) * padicValNat p 24)) := by
  sorry

end Apery
