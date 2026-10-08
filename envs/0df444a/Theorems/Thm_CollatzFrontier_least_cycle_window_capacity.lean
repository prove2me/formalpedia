-- Prove2me | Theorems.Thm_CollatzFrontier_least_cycle_window_capacity
-- name    : CollatzFrontier.least_cycle_window_capacity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:58:59.678908+00:00
-- url     : https://prove2.me/theorems/190f9432-2f0d-49a4-9a03-05da87e148e7
-- title:
--   Realized Syracuse cycles need enough valuation-window labels for their states
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$ be the Syracuse map and let $v_2$ denote the exponent of two. Suppose $m$ is odd, $p>0$, and $T^p(m)=m$, so $m$ lies on a period-$p$ orbit. Suppose further that $p$ is the exact (least) period: $T^d(m)\ne m$ for every $0<d<p$. Suppose every state visited by the orbit lies in a known interval: $L\le T^d(m)\le U$ for all $d<p$.
--
--   For a start index $i$, the length-$k$ *orbit valuation window* beginning at $i$ (`Definitions.Def_collatzFrontierWordWindows`, `orbitValuationWindow`) records the next $k$ dyadic valuations along the orbit,
--   $$\bigl(v_2(3\,T^{i}(m)+1),\dots,v_2(3\,T^{i+k-1}(m)+1)\bigr).$$
--
--   Then
--   $$p \;\le\; \#\{\text{distinct orbit valuation windows at scale }k\}\cdot\Bigl(\Bigl\lfloor\tfrac{U-L}{2\cdot3^k}\Bigr\rfloor+1\Bigr).$$
--
--   Equivalently: a realized Syracuse cycle of period $p$ must either visit a wide range of states, or exhibit many distinct length-$k$ valuation windows -- it cannot have both a narrow state range and highly repetitive windows while staying as long as $p$.
--
--   This is the realized-orbit counterpart of the word-level theorem `CollatzFrontier.primitive_word_nondivisibility_of_window_capacity`, proved for an actual Syracuse-periodic point rather than for an abstract candidate word; the word-level theorem is obtained from this one by transporting the packing argument across the exact correspondence between a primitive word under the platform's canonical divisibility condition and its realized state. Taken alone it supplies no new numeric exclusion (it does not lower the mission's $6291$ period floor); its value is as a general capacity inequality that can be applied directly to a conjectured or partially known cycle, without first assembling a formal word for it.
--
--   **Formalization Note.** `hcyc` together with `hmin` says $p$ is the exact least period of $m$ under $T$, not merely some period; `hbounds` is a known interval for the orbit states, supplied as a hypothesis rather than derived.
-- source:
--   Original result of this contribution. Private repository collatz-frontier, branch research/window-complexity-20261002, commit a3a13a7cb543ccbc29d83fe91aaa68f59fa13874, file lean/CollatzFrontier/WindowComplexity.lean, declaration CollatzFrontier.least_cycle_window_capacity, doc docs/window-complexity.md. Uses only the platform Syracuse step Definitions.Def_syracuseStep and Mathlib's minimal-period API (Mathlib.Dynamics.PeriodicPts.Defs); feeds the word-level corollary CollatzFrontier.primitive_word_nondivisibility_of_window_capacity submitted alongside it.

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_collatzFrontierWordWindows

namespace CollatzFrontier

theorem least_cycle_window_capacity (m p k L U : ℕ) (hp : 0 < p) (hodd : Odd m)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ d : ℕ, 0 < d → d < p → syracuseStep^[d] m ≠ m)
    (hbounds : ∀ d : ℕ, d < p → L ≤ syracuseStep^[d] m ∧ syracuseStep^[d] m ≤ U) :
    p ≤ ((Finset.univ : Finset (Fin p)).image
        (fun i : Fin p => orbitValuationWindow m k i.val)).card * ((U - L) / (2 * 3 ^ k) + 1) := by sorry

end CollatzFrontier
