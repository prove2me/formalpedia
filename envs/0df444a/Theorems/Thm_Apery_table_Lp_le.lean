-- Prove2me | Theorems.Thm_Apery_table_Lp_le
-- name    : Apery.table_Lp_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:25:31.355092+00:00
-- url     : https://prove2.me/theorems/9c671271-e1b6-4358-995d-600d717ea94f
-- title:
--   Inner bound in continuous form: $-L_p \le p\,E_{\mathrm{in}}(K/p,k) + C_{\mathrm{tab}}$
-- statement:
--   Under the same side conditions as `Apery.inner_Lp_le` and for every level $k$ in the admissible window, the local exponent is bounded by the continuous inner profile:
--
--   $$-L_p \;\le\; p\,E_{\mathrm{in}}\Bigl(\frac{K}{p},\, k\Bigr) + C_{\mathrm{tab}}(n,p,k).$$
--
--   This is `table_Lp_le` of `Apery/Growth/TablePrime.lean`: the discrete bound `Apery.inner_Lp_le` with the layer sum replaced by `2J`, the class sum by its continuous limit (`Apery.class_sum_approx`), and the floors/fractional parts evaluated. **Formalization Note** `Lp`, `Ein`, `Ctab`, `Mcut` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/TablePrime.lean#L36-L81

import Mathlib
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceGrowthErrors

open Finset

namespace Apery

theorem table_Lp_le {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (hn : 33 ≤ n)
    (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p) (hsmall : ¬ p * Mcut ≤ 40 * n)
    (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (k : ℤ) (hk1 : kloI n p ≤ k) (hk2 : k ≤ ktopI n p) :
    -(Lp n p : ℝ) ≤ (p : ℝ) * Ein (40 * n / p) k + Ctab n p k := by
  sorry

end Apery
