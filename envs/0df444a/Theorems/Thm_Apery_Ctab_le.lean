-- Prove2me | Theorems.Thm_Apery_Ctab_le
-- name    : Apery.Ctab_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:23:48.649769+00:00
-- url     : https://prove2.me/theorems/d34fca83-480e-404b-8c34-0ec7c780e29e
-- title:
--   Table error bound: $C_{\mathrm{tab}} \le 10^8$
-- statement:
--   Whenever $\lfloor 40n/p\rfloor \le 20$ and $k$ lies in the admissible window, the additive error of the continuous inner bound is bounded by the explicit constant $10^8$: $C_{\mathrm{tab}}(n,p,k) \le 10^8$. This is `Ctab_le` of `Apery/Growth/Assembly2.lean` (via `sum_abs_bIn_le`, `Bmax_le`, `ktop_sub_klo`). **Formalization Note** `Ctab`, `kloI`, `ktopI` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly2.lean#L58-L73

import Mathlib
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceGrowthErrors

open Finset

namespace Apery

lemma Ctab_le {n p : ℕ} (hq : 40 * n / p ≤ 20) {k : ℤ} (hk1 : kloI n p ≤ k)
    (hk2 : k ≤ ktopI n p) : Ctab n p k ≤ 10 ^ 8 := by
  sorry

end Apery
