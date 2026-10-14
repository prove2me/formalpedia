-- Prove2me | Theorems.Thm_Apery_crude_tauX
-- name    : Apery.crude_tauX
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T19:22:18.343051+00:00
-- url     : https://prove2.me/theorems/d6ffbd6f-0501-431b-8086-1bee7c7896d4
-- title:
--   Residue bound for $\tau_X$ on the poles $\pm 1,\dots,\pm K$: $v_p^G \ge -6\log_p(d+1) - v_p(24)$
-- statement:
--   **Lemma 3.3 (crude) for the poles $\pm 1,\dots,\pm K$.** Let $K \ge 1$, $2K \le d$, $A \in \mathbb{Q}[X]$ of degree $\le d$ whose integer values are $p$-adically integral ($\mathrm{VG}\,p\,(A(z))\,0$ for all $z \in \mathbb{Z}$). Then the functional $\tau_X$ applied to $A(x)\cdot(K!)^2$ with pole set $\{ \pm 1, \dots, \pm K \}$ has Gauss valuation at least $-6\log_p(d+1) - v_p(24)$. This is `crude_tauX` of `Apery/Arith/SmallPrimeTau.lean`; it is the residue computation underlying the small-prime bound `Apery.small_prime_bound` (hence `Apery.integral_mN`). **Formalization Note** `tauX`, `resP`, `piPl`, `polyPart`, `dd`, `Lb`, `bin`, `tau`, `BinRep`, `res` are platform definitions of `Zeta5_SourcePoleFun`; `GV`, `VG`, `PlK` are as before.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/SmallPrimeTau.lean#L81-L193 (+ SmallPrimeRes.lean, SmallPrime.lean, PoleFun.lean, Pullback.lean card_PlK)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem crude_tauX {K d : ℕ} (hK : 1 ≤ K) (hdK : 2 * K ≤ d) (A : ℚ[X]) (hA : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) :
    GV p (tauX (C ((K.factorial : ℚ) ^ 2) * A) (PlK K))
      (-6 * (Nat.log p (d + 1) : ℚ) - padicValNat p 24) := by
  sorry

end Apery
