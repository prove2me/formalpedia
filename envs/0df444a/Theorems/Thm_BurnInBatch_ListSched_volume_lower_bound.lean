-- Prove2me | Theorems.Thm_BurnInBatch_ListSched_volume_lower_bound
-- name    : BurnInBatch.ListSched.volume_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:06:46.630008+00:00
-- url     : https://prove2.me/theorems/419b23b5-7175-4863-99e7-69e507aedfee
-- title:
--   Proof of Proposition 1 — processing-volume lower bound
-- statement:
--   Consider $n>0$ jobs with positive processing times $p_j$, batch capacity $B>0$, and $m>0$ identical parallel batch machines. If $C_{\max}^*$ is the minimum makespan over all valid batchings and machine assignments, then
--
--   $$
--   \frac{1}{mB}\sum_{j=1}^{n}p_j\le C_{\max}^*.
--   $$
--
--   This lower bound compares the aggregate processing volume with the total batch capacity available across the machines. It is the volume estimate used in Proposition 1.
--
--   **Formalization Note** The paper uses one-based job indices; Lean uses `Fin n`. Job processing times are real and strictly positive. The optimal makespan ranges over all valid batchings, including partial and nonconsecutive batches.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 772, proof of Proposition 1, display “(1/mB) Σ p_i ≤ C_max*”; https://doi.org/10.1287/opre.40.4.764

import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proof of Proposition 1, p. 772: total job processing volume divided by `mB`
is a lower bound for the optimum batch makespan. -/
theorem volume_lower_bound {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (hn : 0 < n) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) :
    (∑ j : Fin n, p j) / ((m : ℝ) * (B : ℝ)) ≤
      CmaxStar p B m Finset.univ := by sorry

end BurnInBatch.ListSched
