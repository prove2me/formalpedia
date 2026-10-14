-- Prove2me | Theorems.Thm_Apery_VG_eval_int_of_window
-- name    : Apery.VG_eval_int_of_window
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:57:35.88216+00:00
-- url     : https://prove2.me/theorems/53494ca7-576a-4772-8d18-0d3e4939733a
-- title:
--   Integer-window valuation bound: $\mathrm{VG}\,p\,(P(z))\,\beta$ for all $z \in \mathbb{Z}$
-- statement:
--   Let $p$ be prime and $P \in \mathbb{Q}[X]$ with $\deg P \le d$. If all $d+1$ values $P(s), P(s+1), \dots, P(s+d)$ of $P$ at consecutive integers are $p$-adically bounded below by $\beta$ (in the sense $\mathrm{VG}\,p\,(P(s+i))\,\beta$, i.e. either the value vanishes or $\beta \le v_p$ of it), then *every* integer value $P(z)$, $z \in \mathbb{Z}$, is bounded in the same way. This is `VG_eval_int_of_window` of `Apery/Arith/SmallPrime.lean`, proved from the binomial basis (`newton`), the Bernoulli functional bound `tau_bound` and the valuation toolkit `VG`/`GV`. It is the integer-point input of the small-prime bound for `Apery.integral_mN`. **Formalization Note** `VG` is the platform definition of `Zeta5_SourceValToolkit`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/SmallPrime.lean#L54-L80 (+ BinomBasis.lean, TauBound.lean, IntPoly.lean, Val.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem VG_eval_int_of_window {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) (s : ℤ) {β : ℚ}
    (hv : ∀ i ≤ d, VG p (P.eval ((s + i : ℤ) : ℚ)) β) (z : ℤ) : VG p (P.eval (z : ℚ)) β := by
  sorry

end Apery
