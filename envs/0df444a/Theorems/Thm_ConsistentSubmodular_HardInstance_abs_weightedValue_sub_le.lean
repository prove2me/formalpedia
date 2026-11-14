-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_abs_weightedValue_sub_le
-- name    : ConsistentSubmodular.HardInstance.abs_weightedValue_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:35.852203+00:00
-- url     : https://prove2.me/theorems/d893a6a3-a922-4449-82b4-4b122762faa2
-- title:
--   Perturbing the weights of groups $1$ and $2$ changes weighted coverage by at most $2\delta k$
-- statement:
--   In the hard stream on $3k+2$ elements, let $u,v:\{0,1,2\}\to\mathbb R$ be two weight vectors and $\delta\in\mathbb R$ such that $v_0=u_0$, $|v_1-u_1|\le\delta$ and $|v_2-u_2|\le\delta$. Let $f_w(T)=\sum_g w_g\cdot\#\{\text{cells of group } g \text{ covered by } T\}$ denote the weighted coverage with weights $w$. Then for every family $T$ of stream elements,
--   $$\bigl|f_v(T)-f_u(T)\bigr|\le 2\delta k.$$
--
--   A family covers at most $k$ cells of each group, so changing the weights of groups $1$ and $2$ by at most $\delta$ each changes the weighted coverage by at most $2\delta k$. This is used to pass from the weights of the linear program to nearby weights in the hard instance of Appendix A.2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean#L338-L363 (`ConsistentSubmodular.HardInstance.abs_weightedValue_sub_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance
variable {k : ℕ} {u : Fin 3 → ℝ}

theorem ConsistentSubmodular.HardInstance.abs_weightedValue_sub_le {v : Fin 3 → ℝ} {δ : ℝ} (h0 : v 0 = u 0)
    (h1 : |v 1 - u 1| ≤ δ) (h2 : |v 2 - u 2| ≤ δ) (T : Finset (Fin (3 * k + 2))) :
    |weightedValue k v T - weightedValue k u T| ≤ 2 * δ * k := by sorry
