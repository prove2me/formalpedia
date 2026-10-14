-- Prove2me | Theorems.Thm_Apery_outer_entry
-- name    : Apery.outer_entry
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T21:55:34.449148+00:00
-- url     : https://prove2.me/theorems/c3fdb490-3b31-41ae-b916-70741a59c8b6
-- title:
--   The outer-range entry bound: $v_p^G(\mu_X(tpol) - \mu_{\ge}(tpol/D)) \ge wO(c_s,i_s) + wO(c_t,i_t)$
-- statement:
--   **The outer-range entry bound (4.11).** Let $p \ge 7$ with $40n < 3p$, $2 \cdot 40n < p^2$ and $3n < p$, and let $(c_s, i_s)$, $(c_t, i_t)$ be two rows of the outer basis. Then the entry $\mu_X(tpol\,entryO) - \mu_{\ge}(tpol\,entryO / D_{40n})$ has Gauss valuation at least $wO(c_s, i_s) + wO(c_t, i_t)$. This is `outer_entry` of `Apery/Arith/OuterEntryMain.lean`: writing $\mu_X = \mu_{\ge} + \mu_{<}$, the pole analysis of the entry via the residues of $tpol\,entryO$ against the tail poles, including the pairing lemma for the last two poles of a class. It is the entry bound consumed by `Apery.outer_bound`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/OuterEntryMain.lean#L462-L481

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourceOuter
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

namespace Apery

theorem outer_entry {m p : ℕ} [hp : Fact p.Prime] (hm : 2 * m + 1 = p) (n : ℕ)
    (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    GV p (μX (40 * n) (tpol (entryO hm n cs is ct it)) -
      C (μGe p (tpol (entryO hm n cs is ct it) /ₘ D (40 * n)))) (wO hm n cs is + wO hm n ct it) := by
  sorry

end Apery
