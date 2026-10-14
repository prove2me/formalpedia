-- Prove2me | Theorems.Thm_Apery_muX_tpol_bound
-- name    : Apery.muX_tpol_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T20:27:17.331768+00:00
-- url     : https://prove2.me/theorems/c317b51c-1ed4-4546-9f9c-09b1d2c1eebc
-- title:
--   Entry bound: $v_p^G(\mu_X(tpol\,M/D_K)) \ge \min_c(e_c - \ell_c) - 4$
-- statement:
--   **Entry bound (4.5).** Let $p \ge 5$, $K < p^2$, $M$ a multiset of integers with $5 + 2|M| - 2K + 1 < p^2$, and $PlK\,K$ the poles $\pm 1, \dots, \pm K$ ($p$-separated). If $\beta \le e_c - \ell_c$ for every residue class $c \bmod p$, where $e_c = [c = 0]\cdot 5 + \#\{\gamma \in M : \gamma \equiv c\} + \#\{\gamma \in M : \gamma \equiv -c\}$ and $\ell_c = \#\{r \in PlK\,K : r \equiv c\}$, then $v_p^G(\mu_X(tpol\,M / D_K)) \ge \beta - 4$, where $tpol\,M = \prod_{\gamma \in M} (t + \gamma^2)$. This is `μX_tpol_bound` of `Apery/Arith/TEntry.lean`; it is the entry estimate used by the class-basis framework `class_frame` toward `Apery.inner_bound_cap`. **Formalization Note** `Sep`, `PlK`, `μX`, `GV` are platform definitions; `tpol`, `plc` of `Zeta5_SourceInner`. The published name is ASCII `muX_tpol_bound` (source `μX_tpol_bound`).
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/TEntry.lean (+ DirectPoly.lean, DirectBound.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem muX_tpol_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (K : ℕ) (M : Multiset ℤ)
    (hsep : Sep p (PlK K)) (hK : K < p ^ 2) (hdeg : 5 + 2 * M.card - 2 * K + 1 < p ^ 2) (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ ((if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) - (plc p (PlK K) c).card) :
    GV p (μX K (tpol M)) (β - 4) := by
  sorry

end Apery
