-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_priority_vector_unique_solution_eq5
-- name    : CoffmanMitrani1980.Region.priority_vector_unique_solution_eq5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:15:53.739169+00:00
-- url     : https://prove2.me/theorems/7867911d-8515-4d41-8e78-df0175653c71
-- title:
--   Lemma 2, proof — the preemptive priority vector is the solution of (5) for its chain of top sets
-- statement:
--   Fix the model parameters ($\lambda_i,\mu_i>0$, $\rho<1$) and a priority order $i_1,\dots,i_M$, with top sets $S_k=\{i_1,\dots,i_k\}$. For a vector $W\in\mathbb R^M$, the $M$ equations
--   $$\sum_{i\in S_k}\rho_iW_i=\frac{\sum_{i\in S_k}\rho_i/\mu_i}{1-\sum_{i\in S_k}\rho_i},\qquad k=1,\dots,M,$$
--   hold if and only if $W=P(i_1,\dots,i_M)$, the preemptive priority vector of that order.
--
--   This is the closing remark of the proof of Lemma 2: a vertex of $H^{**}$ whose tight sets form this chain is the priority vector $P(i_1,\dots,i_M)$.
--
--   **Formalization Note.** The priority order is a permutation `π` of `Fin M` with rank $0$ highest, and $S_k$ is `topSet π k`.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, p. 818, Lemma 2, proof: equations (5) and the final sentence of the proof

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- Coffman and Mitrani, Operations Research 28 (1980), p. 818 (PDF 10), Lemma 2, proof, equations (5):
"The proof of Lemma 2 is completed by remarking that the solution of (5), for these subsets of job
class indices, is precisely P(i₁, i₂, ···, i_M)." For the chain of top sets `S_k = {i₁, …, i_k}`,
`k = 1, …, M`, of a priority order, a vector `W` satisfies the `M` equations
`Σ_{i∈S_k} ρᵢ Wᵢ = f(S_k)` if and only if `W = P(i₁, …, i_M)`.

**Formalization Note.** The priority order is `π : Equiv.Perm (Fin M)` (rank `0` highest), and
`S_{k+1} = topSet π (k+1)` for `k : Fin M`. -/
theorem priority_vector_unique_solution_eq5 {M : ℕ} (p : Params M) (π : Equiv.Perm (Fin M))
    (W : Fin M → ℝ) :
    (∀ k : Fin M, ∑ i ∈ topSet π ((k : ℕ) + 1), p.rho i * W i = p.f (topSet π ((k : ℕ) + 1))) ↔
      W = p.prioVec π := by sorry

end CoffmanMitrani1980.Region
