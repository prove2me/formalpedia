-- Prove2me | Theorems.Thm_BakerScudder1990_Tolerance_optimality_conditions
-- name    : BakerScudder1990.Tolerance.optimality_conditions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:10:48.274076+00:00
-- url     : https://prove2.me/theorems/f63dd21d-68a5-403e-83e4-46792b5b6254
-- title:
--   Appendix, proof of Property IV(G) — sufficient conditions for $d = C_j - v_j$ and for $d = C_j + u_j$ to be the least optimal due date
-- statement:
--   Consider an instance of the single-machine common-due-date model with tolerances, with jobs in a fixed sequence, completion times $C_1,\dots,C_n$, and fix a job $j$.
--
--   1. If
--   $$
--   \sum_{i<j} \alpha_i < \sum_{i \ge j} \beta_i \quad\text{and}\quad \sum_{i<j} \alpha_i \ge \sum_{i>j} \beta_i ,
--   $$
--   then $d = C_j - v_j$ is the least optimal due date.
--   2. If
--   $$
--   \sum_{i<j} \alpha_i < \sum_{i>j} \beta_i \quad\text{and}\quad \sum_{i\le j} \alpha_i \ge \sum_{i>j} \beta_i ,
--   $$
--   then $d = C_j + u_j$ is the least optimal due date.
--
--   In each case the strict inequality says the penalty strictly decreases as $d$ approaches the point from the left, and the weak inequality says it does not decrease to the right. Relabelling $j$ as $b$, these are the two cases of Property IV(G).
--
--   **Formalization Note** The paper writes "the conditions for $d = C_j - v_j$ to be optimal are …"; they are stated here as sufficient conditions for being the *least* optimal due date, which is how the proof uses them. The converse is not stated: it fails when $u_j = v_j = 0$, where the two points coincide and either pair suffices. Positions are 0-based ($k = j-1$); the sums run over positions $i<k$, $i \ge k$, $i>k$, $i \le k$.
-- source:
--   Baker and Scudder, Sequencing with earliness and tardiness penalties: a review, Oper. Res. 38 (1990), p. 35, Appendix, proof of Property IV(G), the conditions for d = C_j − v_j and for d = C_j + u_j to be optimal

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Appendix, proof of Property IV(G), the two optimality conditions (Baker and Scudder 1990,
p. 35), as sufficient conditions. For the job in 0-based position `k`:
(1) if `∑_{i<k} α_i < ∑_{i≥k} β_i` and `∑_{i<k} α_i ≥ ∑_{i>k} β_i`, then `d = C_k - v_k` is the
least optimal due date;
(2) if `∑_{i<k} α_i < ∑_{i>k} β_i` and `∑_{i≤k} α_i ≥ ∑_{i>k} β_i`, then `d = C_k + u_k` is the
least optimal due date. -/
theorem optimality_conditions {n : ℕ} (I : Instance n) (k : Fin n) :
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) →
      I.IsLeastOptimalDueDate (I.C k - I.v k)) ∧
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i) →
      I.IsLeastOptimalDueDate (I.C k + I.u k)) := by sorry

end BakerScudder1990.Tolerance
